open HolKernel Parse boolLib bossLib;
open ffiTheory;
open spi_hostRegsTheory;
open BasicProvers;

val _ = new_theory("spi_hostCore");

Datatype:
  fsmState =
    Idle
  | ConfigSwitch
  | WaitLead
  | IntClockHigh
  | IntClockLow
  | IdleCSBActive
  | WaitTrail
  | WaitIdle
End

Datatype: 
  configopts = <|
    clkdiv: 16 word;
    csnidle: 4 word;
    csntrail: 4 word;
    csnlead: 4 word;
    fullcyc: 1 word;
    cpha: 1 word;
    cpol: 1 word;
  |>
End

Datatype:
  command = <|
    csid: 1 word; (* TODO csid needs a CSW defined length, put constant how do this? *)
    speed: 2 word;
    wr_en: bool;
    rd_en: bool;
    len: 9 word;
    csaat: 1 word;
  |>
End

Datatype:
  tx_data = <|
    data: 32 word;
    be: 4 word;
  |>
End

val command_depth = 64;
val rx_fifo_depth = 64;
val tx_fifo_depth = 72;
val num_cs = 1;

Datatype:
  spi_host_state = <|
    (* An infinite stream of non-deterministic numbers used to determine what in the
     * hardware's state has changed since the last shared memory access.
     *
     * This is inspired by `CakeML/hardware`'s `fbits`; we use `num`s instead of
     * bits because with bits, it's tricky to define how they're interpreted to
     * produce the number of ticks that pass between each read/write. My initial
     * idea was to interpret each bit as 'should we keep going', and thus end up
     * using the number of leading ones as the number of ticks; however, if `fbits`
     * was all 1s, that would cause `apply_fbits` not to terminate. With `num`s, we
     * can just take the first `num` from the list and use that as the number of
     * ticks.
     *
     * Having a version of this for each peripheral is a bit silly, but should allow
     * proving theorems about each of them independently. *)
    fnums : num -> num;
    regs : spi_host_regs;
    (* Although there can only be one regbus transaction per clock cycle, because
     * non-`hwext` transactions only issue notifications on the next clock cycle,
     * whereas `hwext` transactions issue notifications immediately, you can end up
     * with two notifications on the same clock cycle if you have a non-`hwext`
     * transaction immediately followed by a `hwext` transaction. *)
    buffered_notif : spi_host_notif option;


    commands: command list;

    config : configopts;
    fsm_state : fsmState;
    clock_counter: 16 word;
    counter : 4 word;
    byte_starting_cpha0: bool;
    bit_shifting_cpha0: bool;
    byte_ending_cpha0: bool;
    bit_counter: 3 word;
    byte_counter: 9 word;
    
    csaat: bool;
    csid: 1 word;
    csid_q: 1 word;
    select_data: 32 word;
    select_be: 4 word;
    select_byte_pos: num;
    select_byte_out: 8 word;
    select_valid_o: bool;

    merge_pos: num;
    merge_word_data: 32 word;

    cmd_wr_en: bool;
    cmd_len: 9 word;
    cmd_speed: 2 word;

    rx_data_fifo: 32 word list;
    tx_data_fifo: tx_data list;

    (* SR state *)
    rx_buf_valid: bool;
    rx_buf: 9 word;
  |>
End

Definition spi_host_configopts_0_to_configopts:
  spi_host_configopts_0_to_configopts (val: spi_host_configopts_0): configopts = 
  <|
    clkdiv := val.clkdiv_0;
    csnidle := val.csnidle_0;
    csntrail := val.csntrail_0;
    csnlead := val.csnlead_0;
    fullcyc := val.fullcyc_0;
    cpha := val.cpha_0;
    cpol := val.cpol_0;
  |>
End

Definition spi_host_eat_fnum:
  spi_host_eat_fnum st = (st with fnums := st.fnums o SUC, st.fnums 0)
End

Definition spi_host_core_command:
  spi_host_core_command(csid: 1 word, update: spi_host_command_update): command =
  <|
    csid := csid;
    speed := update.speed;
    wr_en := word_bit 1 update.direction;
    rd_en := word_bit 0 update.direction;
    csaat := update.csaat;
    len := update.len;
  |>
End

Datatype:
  spi_delay = <|
    csnlead   : 4 word;
    csntrail  : 4 word;
    csnidle   : 4 word;
  |>
End

Definition spi_host_core_no_error:
  spi_host_core_no_error(status: spi_host_error_status): bool =
    (status.cmdbusy = 0w ∧
    status.overflow = 0w ∧
    status.underflow = 0w ∧
    status.cmdinval = 0w ∧
    status.csidinval = 0w ∧
    status.accessinval = 0w)
End

Definition bool2word1:
  bool2word1(b: bool): 1 word = 
    if b then 1w else 0w
End

(* Simulates one clock cycle of the spi_host core.
 *
 * Register reads/writes are handled externally, with new values simply being
 * made available in `st`. If the hardware has a `qe`/`re` signal to detect
 * interactions with a register, a notification is provided that that's occured.
 * For regular registers, this occurs on the clock cycle after the I/O actually
 * occurs, but for `hwext` registers it occurs on the same clock cycle. *)
Definition spi_host_tick_def:
  spi_host_tick (hwext_notif: spi_host_hwext_notif option) (st: spi_host_state): ffi_outcome + spi_host_state =
    let
      fnums = st.fnums;
      command_valid_i: bool = (LENGTH st.commands > 0);
      
      sw_rst_i: bool = word_bit 0 (st.regs.control.sw_rst);
      en_i: bool = ((st.regs.control.spien = 1w) ∧ spi_host_core_no_error(st.regs.error_status));

      fsm_en: bool = (en_i ∧ st.clock_counter = 0w);
      
      empty_command_update: spi_host_command_update = <|len:= 0w; csaat:= 0w; speed:= 0w; direction:= 0w; |>;

      (q: spi_host_command_update, qe: bool) = case hwext_notif of
        SOME (Write (command_write update_val)) => (update_val, T)
        | _ => (empty_command_update, F);

      recv_command: bool = qe;
      command_i: command = spi_host_core_command(st.csid, q);
      commands' = if recv_command then APPEND st.commands [command_i] else st.commands;

      next_command: command = HD st.commands;

      (* command_ready_idle_csb_active: bool = if command_valid_i then ¬(next_command.csid = st.csid_q)
                                              else T; *)
			(* This is a little hacky to reduce the complexity of HOL output *)		      
      command_ready_idle_csb_active: bool = ¬(next_command.csid = st.csid_q);

      command_ready_int: bool = if st.fsm_state = Idle ∨ st.fsm_state = WaitIdle then T
                                else if st.fsm_state = IntClockHigh ∨ st.fsm_state = IdleCSBActive then command_ready_idle_csb_active
                                else F;
      new_command: bool = (command_ready_int ∧ command_valid_i);

      commands'' = if new_command then TL commands' else commands';

      config': configopts = if new_command ∧ (st.regs.csid.csid = 1w) then spi_host_configopts_0_to_configopts(st.regs.configopts_0)
                            else st.config; 
	    (* Could be good to have this all config opts maybe? But we are only dealling with one csid *)

      cmd_speed': 2 word = if new_command then next_command.speed else st.cmd_speed;

      start_bit: 3 word = if cmd_speed' = 0w then 7w else if cmd_speed' = 1w then 6w else 4w;
      shift_size: 3 word = if cmd_speed' = 0w then 1w else if cmd_speed' = 1w then 2w else 4w;

      switch_required: bool = ¬(config' = st.config);

      clock_counter': 16 word = if sw_rst_i then 0w
                                else if ¬en_i then st.clock_counter
                                else if st.fsm_state = Idle ∨ st.fsm_state = IdleCSBActive then 0w
                                else if new_command then st.config.clkdiv
                                else if (st.clock_counter = 0w) then st.config.clkdiv
                                else st.clock_counter - 1w;
      delay: spi_delay = <|
        csnlead   := st.config.csnlead;
        csntrail  := st.config.csntrail;
        csnidle   := st.config.csnidle;
      |>;

      last_bit: bool = (st.bit_counter = 0w);
      last_byte: bool = (st.byte_counter = 0w);

      state_after_idle =  if new_command then
                            if switch_required then ConfigSwitch
                            else WaitLead
                          else Idle;
      state_after_idle_csb_active = if new_command then
                                      if switch_required then WaitTrail
                                      else IntClockLow
                                    else IdleCSBActive;

      fsm_state': fsmState = case st.fsm_state of
          Idle                =>  state_after_idle
        | ConfigSwitch        =>  if st.counter > 1w then ConfigSwitch
                                  else WaitLead
        | WaitLead            =>  if st.counter > 1w then WaitLead
                                  else IntClockHigh
        | IntClockHigh        =>  if last_bit ∧ last_byte then
                                    if st.csaat then state_after_idle_csb_active
                                    else WaitTrail 
                                  else IntClockLow
        | IntClockLow         =>  IntClockHigh
        | IdleCSBActive       =>  state_after_idle_csb_active
        | WaitTrail           =>  if st.counter > 1w then WaitTrail
                                  else WaitIdle
        | WaitIdle            =>  if st.counter > 1w then WaitIdle
                                  else state_after_idle;

      curr_delay: 4 word = case fsm_state' of
          WaitLead => delay.csnlead
        | WaitTrail => delay.csntrail
        | WaitIdle => delay.csnidle
        | ConfigSwitch => delay.csnidle
        | _ => 0w;

      state_changing: bool = ¬(fsm_state' = st.fsm_state);
      counter': 4 word = if state_changing then curr_delay 
                          else if st.counter > 0w then st.counter - 1w 
                          else 0w; 

      cpha: bool = word_bit 0 st.config.cpha;
      
      byte_starting_cpha0': bool = (¬(sw_rst_i) ∧ state_changing ∧
                                  ((fsm_state' = WaitLead) ∨ (fsm_state' = IntClockLow ∧ st.bit_counter = 0w)));

	    byte_starting: bool = if cpha then state_changing ∧ st.byte_starting_cpha0
                            else byte_starting_cpha0';

      
      bit_shifting_cpha0': bool = (¬(sw_rst_i) ∧ state_changing ∧ (fsm_state' = IntClockLow ∧ ¬(st.bit_counter = 0w)));



      bit_shifting = if cpha then st.bit_shifting_cpha0 ∧ state_changing
                      else bit_shifting_cpha0';

      bit_counter_d: 3 word = if sw_rst_i then 0w
                              else if ¬fsm_en then st.bit_counter
                              else if byte_starting then start_bit
                              else if bit_shifting then st.bit_counter - shift_size
                              else st.bit_counter;

      byte_ending_cpha0': bool = (¬(sw_rst_i) ∧ state_changing ∧ ((st.fsm_state = IntClockHigh) ∧ (st.bit_counter = 0w)));
      byte_ending: bool = if cpha then st.byte_ending_cpha0 ∧ state_changing
                          else byte_ending_cpha0';

      csaat_d: bool = if new_command then word_bit 0 command_i.csaat else st.csaat;
      cmd_len_d: 9 word = if new_command then command_i.len else st.cmd_len;
      cmd_wr_en_d: bool = if new_command then command_i.wr_en else st.cmd_wr_en;

      byte_counter_d: 9 word = if sw_rst_i then 0w
                        else if ¬fsm_en then st.byte_counter
                        else if new_command then cmd_len_d
                        else if byte_ending then st.byte_counter - 1w
                        else st.byte_counter;

      sr_wr_ready_i: bool = st.select_valid_o;
      wr_en_internal: bool = (byte_starting ∧ cmd_wr_en_d);



      (* SR output signals *)
      merge_byte_ready_o: bool = ¬(st.merge_pos = 4); (*This is an ugly place to put this but needed for line bellow TODO: clean this up *)

      
      rd_ready_o: bool = ((¬st.rx_buf_valid) ∨ (st.rx_buf_valid ∧ merge_byte_ready_o));
      sr_rd_ready_i: bool = rd_ready_o;

      (* Back to FSM *)
      rd_en_internal: bool = bit_shifting;
      tx_stall_o: bool = (wr_en_internal ∧ ¬sr_wr_ready_i);
      rx_stall_o: bool = (rd_en_internal ∧ ¬sr_rd_ready_i);
      
      stall: bool = (tx_stall_o ∨ rx_stall_o);

      wr_en_o: bool = (wr_en_internal ∧ ¬stall);
      rd_en_fsm_o: bool = (rd_en_internal ∧ ¬stall);


      (* byte select model*)
      tx_data_i: 32 word = (HD st.tx_data_fifo).data;
      tx_be_i: 4 word = (HD st.tx_data_fifo).be;
      word_valid_i: bool = (LENGTH st.tx_data_fifo > 0);
      byte_ready_i: bool = wr_en_o;

      byte_select_advance: bool = (word_valid_i ∨ byte_ready_i ∨ (st.select_byte_pos > 0 ∧ word_bit (4-st.select_byte_pos) st.select_be));
      
      select_data': 32 word = if word_valid_i then tx_data_i else st.select_data;
      select_be': 4 word = if word_valid_i then tx_be_i else st.select_be;
      
      select_byte_en: bool =  if (st.select_byte_pos > 0) then
                                (word_bit (4-st.select_byte_pos) st.select_be)
                              else F;

      select_byte_ready: bool = (byte_ready_i ∧ ((st.select_byte_pos > 0) ∨ select_byte_en));

      select_byte_pos': num = if word_valid_i then 4
                              else if select_byte_ready then 
                                if st.select_byte_pos > 0 then st.select_byte_pos - 1 
                                else st.select_byte_pos
                              else st.select_byte_pos;

      select_word_ready_o: bool = (st.select_byte_pos = 0);

      select_byte_out': 8 word = if byte_select_advance then
                                  (((4-st.select_byte_pos)*8 + 7) >< ((4-st.select_byte_pos) * 8)) st.select_data
                                  else st.select_byte_out;
      
      select_valid_o': bool = if byte_select_advance then word_bit (4-st.select_byte_pos) st.select_be
                              else st.select_valid_o;
      
      (* byte_merge model *)
      merge_byte_in: 8 word = (7 >< 0) st.rx_buf;
      merge_valid_in: bool = st.rx_buf_valid;
      merge_word_ready_in: bool = (LENGTH st.rx_data_fifo < 64);
      
      
      merge_byte_valid: bool = (merge_valid_in ∨ (st.merge_pos < 4));

      
      merge_word_data': 32 word = if merge_byte_valid then (((32 >< 9) (st.merge_word_data << 8)): 24 word) @@ merge_byte_in
                                  else st.merge_word_data;
      
      merge_pos': num = if merge_byte_valid then 
                          if st.merge_pos = 4 then 0
                            else st.merge_pos + 1 
                        else 
                          if merge_word_ready_in then 0 
                          else st.merge_pos;


      merge_word_o: 32 word = st.merge_word_data;
      merge_word_valid_o: bool = (st.merge_pos = 4);
      merge_ready_o: bool = (st.merge_pos < 4);
      
      (*SR control *)
      rx_ready_sr_i: bool = merge_ready_o;
      rx_buf_valid': bool = if sw_rst_i then F
                            else if rd_en_fsm_o ∧ rd_ready_o then T
                            else if st.rx_buf_valid ∧ rx_ready_sr_i then F
                            else st.rx_buf_valid;

      (* ----- End of FSM ------ *)
      bit_counter': 3 word = if stall then st.bit_counter else bit_counter_d;
      byte_counter': 9 word = if stall then st.byte_counter else byte_counter_d;
      cmd_len': 9 word = if new_command ∧ ¬stall then cmd_len_d else st.cmd_len;
      
      cmd_wr_en': bool = if new_command ∧ ¬stall then cmd_wr_en_d else st.cmd_wr_en;
      csaat': bool = if new_command ∧ ¬stall then csaat_d else st.csaat;
      
      csid': 1 word = if new_command then command_i.csid else st.csid_q;
      csid_q': 1 word = if new_command ∧ ¬stall then st.csid else st.csid_q;

      (* Adding to data_fifos *)
      (tx_word: word32, tx_be: num, q_tx: bool) = case hwext_notif of
        SOME (Write (txdata_write be num1 word32)) => (word32, be, T)
        | _ => (0w, 0, F);
        
      tx_be_w: 4 word = n2w $ tx_be;
      tx_data_new: tx_data =  <|
        data := tx_word;
        be := tx_be_w; 
      |>;
      (*^For be: I don't actually know where this comes from the documentation doesn't even mention this exists *)
      tx_ready_o: bool = (select_word_ready_o ∧ q_tx);
      tx_data_fifo': tx_data list = if tx_ready_o then APPEND st.tx_data_fifo [tx_data_new] else st.tx_data_fifo;

      rx_valid: bool = merge_word_valid_o;
      rx_data_new: 32 word = merge_word_o;
      rx_data_fifo': 32 word list = if rx_valid then APPEND st.rx_data_fifo [rx_data_new] else st.rx_data_fifo;

	
      (* Errors *)
      tx_valid: bool = F; (* Need to get stuff from win reg *)
      access_valid: bool = T;
      error_access_inval: bool = (tx_valid ∧ ¬access_valid);
      command_busy: bool = (LENGTH st.commands < 64);
      error_csid_inval: bool = (command_valid_i ∧ command_busy ∧ ¬(st.regs.csid.csid < 1w));
      error_cmd_inval: bool  = (command_valid_i ∧ command_busy 
                          ∧ ¬((command_i.speed = 0w) ∨ ((command_i.speed < 3w) ∧ ¬(command_i.wr_en = command_i.rd_en))));

      error_overflow: bool = (tx_valid ∧ ¬tx_ready_o);
      (*rx_ready_i into core*)
      error_underflow: bool = (merge_word_ready_in ∧ ¬rx_valid);
      error_busy: bool = (command_valid_i ∧ ¬command_busy);

      error_stat: spi_host_error_status = <|
        cmdbusy := bool2word1(error_busy);
        overflow := bool2word1(error_overflow);
        underflow := bool2word1(error_underflow);
        cmdinval := bool2word1(error_cmd_inval);
        csidinval := bool2word1(error_csid_inval);
        accessinval := bool2word1(error_access_inval);
      |>;

      
      regs' = st.regs with <| error_status := error_stat |>;

      fnums' = λn. fnums (n + 2);
    in
      INR <|
        fnums := fnums';
        buffered_notif := NONE;
        regs := regs';
        clock_counter := clock_counter';
        counter := counter';
        fsm_state := fsm_state';
        byte_starting_cpha0 := byte_starting_cpha0';
        bit_shifting_cpha0 := bit_shifting_cpha0';
        csaat := csaat';
        csid := csid';
        csid_q := csid_q';
        select_data := select_data';
        select_byte_pos := select_byte_pos';
        select_byte_out := select_byte_out';
        select_valid_o := select_valid_o';
        merge_word_data := merge_word_data';
        merge_pos := merge_pos';

        cmd_wr_en := cmd_wr_en';
        cmd_len := cmd_len';
        bit_counter := bit_counter';
        byte_counter := byte_counter';
        byte_ending_cpha0 := byte_ending_cpha0';

        commands := commands'';
        rx_buf_valid := rx_buf_valid';

        cmd_speed := cmd_speed';

        tx_data_fifo := tx_data_fifo';
        rx_data_fifo := rx_data_fifo';
      |>
End

(* Stubs *)
Definition spi_host_txdata_read_def:
  spi_host_txdata_read (st: spi_host_state) (nb: num) (offset: num) = 0w: word32
End

Definition spi_host_rxdata_read_def:
  spi_host_rxdata_read (st: spi_host_state) (nb: num) (offset: num) = 0w: word32
End

Theorem spi_host_tick_buffered_notif_NONE:
  spi_host_tick notif st = INR st' ==> st'.buffered_notif = NONE
Proof
  pure_rewrite_tac [spi_host_tick_def] >>
  LET_ELIM_TAC >>
  simp []
QED

Theorem spi_host_tick_unused_fnums:
  ?n. !fnums. (!i. i < n ==> fnums i = st.fnums i) ==>
  spi_host_tick notif (st with fnums := fnums) =
  SUM_MAP I (\st'. st' with fnums := (\i. fnums (i + n))) (spi_host_tick notif st)
Proof
  qexists `2` >> 
  pure_rewrite_tac [spi_host_tick_def] >>
  LET_ELIM_TAC >>
  gvs [SF ETA_ss]
QED

Theorem unused_fnums_ignored_fnums_val:
  (!fnums. (!i. i < n ==> fnums i = st.fnums i)
    ==> f (st with fnums := fnums) = f st with fnums := (\i. fnums (i + n)))
  ==> (f st).fnums = (\i. st.fnums (i + n))
Proof
  rpt strip_tac
  >> first_x_assum $ qspec_then `st.fnums` assume_tac
  >> `st with fnums := st.fnums = st` by simp [theorem "spi_host_state_component_equality"]
  >> fs []
  >> last_x_assum (fn thm => simp [Once thm])
QED

val _ = export_theory();
