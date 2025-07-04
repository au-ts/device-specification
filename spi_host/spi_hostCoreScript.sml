open HolKernel Parse boolLib bossLib;
open spi_hostRegsTheory;

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

(* I don't think this has the packing? Is a TOFIX *)
Datatype: 
  configopts = <|
    clkdiv: 16 word;
    csnidle: 4 word;
    csntrail: 4 word;
    csnlead: 4 word;
    reserved: 1 word;
    fullcyc: 1 word;
    cpha: 1 word;
    cpol: 1 word;
  |>
End

Datatype: 
  segment = <|
    speed: 2 word;
    cmd_wr_en: 1 word;
    cmd_rd_en: 1 word;
    len: 9 word;
    csaat: 1 word;
  |>
End

Datatype:
  command = <|
    csid: 1 word; (* TODO csid needs a CSW defined length, put constant how do this? *)
    segment: segment;
    config: configopts;
  |>
End




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


    config : configopts;
    fsm_state : fsmState;
    counter : 4 word;
    new_command: bool;
    switch_required: bool;
    bit_counter: 3 word;
    last_bit: bool;
    byte_counter: 9 word;
    last_byte: bool;
    csaat: bool;
    csid: 1 word;
    csid_q: 1 word;
    stall: bool;
    cmd_wr_en: bool;
    cmd_len: 9 word;


    (* Potential constants *)

    (* Both of these depend on kind of SPI standard/dual/quad, but we are likely to only consider standard 
     It is however possible for these values to be modified in execution; 
     I guess so a host can communicate with devices that support varied SPI standards *)
    start_bit: 3 word; (* 7 *)
    shift_size: 3 word; (* 1 *)

    (* SR state *)
    rx_buf_valid: bool;
  |>
End


Definition spi_host_eat_fnum:
  spi_host_eat_fnum st = (st with fnums := st.fnums o SUC, st.fnums 0)
End

Datatype:
  delay = <|
    csnlead   : 4 word;
    csntrail  : 4 word;
    csnidle   : 4 word;
  |>
End


(* Simulates one clock cycle of the spi_host core.
 *
 * Register reads/writes are handled externally, with new values simply being
 * made available in `st`. If the hardware has a `qe`/`re` signal to detect
 * interactions with a register, a notification is provided that that's occured.
 * For regular registers, this occurs on the clock cycle after the I/O actually
 * occurs, but for `hwext` registers it occurs on the same clock cycle. *)
Definition spi_host_tick_def:
  spi_host_tick (hwext_notif: spi_host_hwext_notif option) (st: spi_host_state) =
    let
      fnums = st.fnums;

      delay = <| 
        csnlead   := st.config.csnlead; (* TODO *)
        csntrail  := st.config.csntrail;
        csnidle   := st.config.csnidle;
      |>;

      curr_delay = case st.fsm_state of 
          WaitLead => delay.csnlead
        | WaitTrail => delay.csntrail
        | WaitIdle => delay.csnidle
        | CSBSwitch => delay.csnidle
        | _ => 0w;

      fsm_state' = case st.fsm_state of 
          Idle                =>  if st.new_command then
                                    if st.switch_required then ConfigSwitch
                                    else WaitLead
                                  else Idle
        | ConfigSwitch        =>  if st.counter > 1w then ConfigSwitch
                                  else WaitLead
        | WaitLead            =>  if st.counter > 1w then WaitLead
                                  else IntClockHigh
        | IntClockHigh        =>  if st.last_bit ∧ st.last_byte then
                                    if st.csaat then 
                                      if st.new_command then
                                        if st.switch_required then WaitTrail
                                        else IntClockLow
                                      else IdleCSBActive (* Potential bypass of IdleCSBActive state *)
                                    else WaitTrail 
                                  else IntClockLow
        | IntClockLow         =>  IntClockHigh
        | IdleCSBActive       =>  if st.new_command then
                                    if st.switch_required then WaitTrail
                                    else IntClockLow
                                  else IdleCSBActive  
        | WaitTrail           =>  if st.counter > 1w then WaitTrail
                                  else WaitIdle
        | WaitIdle            =>  if st.counter > 1w then WaitIdle
                                    else 
                                      if st.new_command then
                                        if st.switch_required then ConfigSwitch
                                          else WaitLead
                                      else Idle; (* Potential bypass of Idle state *)

      
      state_changing = fsm_state' != st.fsm_state;
      counter' = if state_changing then delay 
                  else if st.counter > 0w then st.counter - 1w 
                       else 0w; 
      
      
      (* fnums 0 used for command_valid_i *)
      command_valid_i : 1 word = n2w $ fnums 0;

      sw_rst_i: bool = word_bit 0 (n2w $ fnums 1); (*TODO*)
      fsm_en: bool = word_bit 0 (n2w $ fnums 2);
      
      command_i: command;
      (* fnums 1 used for command_i *)
      (* csid_i : 1 word = n2w $ fnums 1;
      
      command_i.csid = csid_i; *)

      command_ready_idle_csb_active : bool =  if command_valid_i = 0w then F
                                              else (command_i.csid = st.csid_q);

      command_ready_int: bool = if st.fsm_state = Idle ∨ st.fsm_state = WaitIdle then T
                                else if st.fsm_state = IntClockHigh ∨ st.fsm_state = IdleCSBActive then command_ready_idle_csb_active
                                else F;
      (* Done in assign this might not be right way to model? *)
      new_command': bool = (command_ready_int ∧ (word_bit 0 command_valid_i));

      bit_counter_d = if sw_rst_i then 0w
                      else if ¬fsm_en then st.bit_counter
                      else if st.byte_starting then st.start_bit
                      else if st.bit_shifting then st.bit_counter - st.shift_size
                      else st.bit_counter;

      byte_starting_cpha0 = (¬(sw_rst_i) ∧ state_changing ∧ 
                            ((st.fsm_state = WaitLead) ∨ (st.fsm_state = IntClockLow ∧ st.bit_counter = 0)));

	    byte_starting' = (byte_starting_cpha0 ∧ (if cpha then state_changing else T));


      bit_shifting_cpha0 = ((sw_rst_i = F) ∧ state_changing ∧ (st.fsm_state = IntClockLow ∧ st.bit_counter != 0));

      bit_shifting' = (bit_shifting_cpha0 ∧ (if cpha then state_changing else T));

      bit_counter' = if st.stall then st.bit_counter else bit_counter_d;
      last_bit' = (st.bit_counter = 0w);

      cmd_len' = if st.new_command then command_i.segment.len else st.cmd_len;

      byte_ending_cpha0 = (¬(sw_rst_i) ∧ state_changing ∧ (st.fsm_state = IntClockHigh ∧ st.bit_counter = 0));
      byte_ending' = (byte_ending_cpha0 ∧ (if cpha then state_changing else T));

      byte_counter_d = if sw_rst_i then 0w
                        else if ¬fsm_en then st.byte_counter
                        else if st.new_command then cmd_len
                        else if st.byte_ending then st.byte_counter - 1
                        else st.byte_counter;
      byte_counter' = if st.stall then st.byte_counter else byte_counter_d;
      
      
      last_byte' = (st.byte_counter = 0w);

      switch_required' = command_i.csid != csid_q;

      csaat' = if st.new_command then command_i.segment.csaat else st.csaat;

      csid' = if st.new_command then command_i.csid else st.csid_q;
      csid_q' = if st.new_command ∧ (st.stall = F) then st.csid else st.csid_q;

      (*Core in *)
      tx_valid_i: bool = word_bit 0 (n2w $ fnums 3);
      tx_data_i: word 32 = n2w $ fnums 5;
      tx_be_i: word 4 = n2w $ fnums 6;
      rx_ready_i: bool = word_bit 0 (new $ fnums 7);

      (*FSM in *)
      sr_wr_ready_i: bool = tx_valid_sr; (*Goes throught shift register but just assigning wires *)
      sr_rd_ready_i: bool = word_bit 0 (n2w $ fnums 4);
      

      cmd_wr_en' = if st.new_command then command_i.segment.cmd_wr_en else st.cmd_wr_en; (* always_comb *)
      
      wr_en_internal = (byte_starting ∧ st.cmd_wr_en);
      rd_en_internal = bit_shifting;
      (* on assign *)
      tx_stall_o: bool = (wr_en_internal ∧ ¬sr_wr_ready_i);
      rx_stall_o: bool = (wr_en_internal ∧ ¬sr_wr_ready_i);
      
      stall': bool = (tx_stall_o ∨ rx_stall_o);

      fnums' = λn. fnums (n + 2);

      (* byte_select *)
        clr_byte_sel' = flush_i ∧ sw_rst_i; (*flush_i is tx_flush_sr is a TODO*)
        (*FIFO outs *)

        (* byte_valid (rvalid_o) *)
        byte_valid_byte_sel: bool = ¬(st.depth_byte_sel = 0) ∧ ¬st.clr_byte_sel;

        rdata_o_byte_sel = (st.data_byte_sel >>> 9*(st.data_pos_byte_sel));

        (* byte_en (rdata_o ) *)
        byte_en_byte_sel: bool = word_bit 8 word_extract (8, 0) rdata_o_byte_sel;

        (* wready_o *)
        wready_o_fifo_byte_sel: bool = st.depth_byte_sel = 0w ∧ ¬st.clr_byte_sel;

      (* byte_select signals *)
      do_drain_byte_sel: bool = byte_valid_byte_sel ∧ ¬ byte_en_byte_sel;
      byte_ready_byte_sel: bool = wr_en_fsm ∧ do_drain_byte_sel;

      word_data_byte_select =   (((word_bit 3 tx_be_i) << 8 + word_extract (31, 24)) << 27)
                              + (((word_bit 2 tx_be_i) << 8 + word_extract (23, 16)) << 18)
                              + (((word_bit 1 tx_be_i) << 8 + word_extract (15, 8)) << 9)
                              + (((word_bit 0 tx_be_i) << 8 + word_extract (7, 0)))

      (*FIFO control *)
      clear_status_fifo_byte_sel = (byte_ready_byte_sel ∧ st.depth_byte_sel = 1w) ∨ clr_fifo_byte_sel;
      clear_data_fifo_byte_sel = clear_status_fifo_byte_sel;
      load_data_fifo_byte_sel = tx_valid_i ∧ wready_o_fifo_byte_sel;
      pull_data_fifo_byte_sel = byte_valid_byte_sel ∧ byte_ready_byte_sel;

      depth_byte_sel': word 3 = if clear_status_fifo_byte_sel then 0w
                                else if load_data_fifo_byte_sel then 4w
                                else if pull_data_fifo_byte_sel then (st.depth_byte_sel - 1)
                                else if st.depth_byte_sel;
      
      data_pos_byte_sel': num = if clear_status_fifo_byte_sel then 0
                                else if pull_data_fifo_byte_sel then st.data_pos_byte_sel + 1
                                else st.data_pos_byte_sel;

      data_byte_sel': word 36 = if clear_data_fifo_byte_sel then 0w
                                else if load_data_fifo_byte_sel then word_data_byte_select
                                else st.data_byte_sel;
      
      (* byte_select outs *)
      word_ready_o_byte_sel: bool: wready_o_fifo_byte_sel;
      byte_valid_o_byte_sel: bool = byte_valid_byte_sel ∧ byte_en_byte_sel;
      byte_o_byte_sel: word 8 = word_extract (8, 0) rdata_o_byte_sel;
      tx_valid_sr = byte_valid_o_byte_sel;


      (* byte_merge *)
      (* state controls *)
      clr_byte_merge': sw_rst_i;

      wready_byte_merge = ¬st.depth_byte_merge = 4 ∧ ¬st.clr_byte_merge;
      rvalid_byte_merge = st.depth_byte_merge = 4 ∧ ¬st.clr_byte_merge;


      byte_valid_byte_merge = do_fill_byte_merge ∨ rx_valid_sr; (*TODO rx_valid_sr*)

      clear_status_byte_merge = (rx_ready_i ∧ rvalid_byte_merge) ∨ st.clr_byte_merge;
      clear_data_byte_merge = clear_status_byte_merge;
      load_data_byte_merge = byte_valid_byte_merge ∧ wready_byte_merge;

      wdata_i_byte_merge: word 8 = if do_fill_byte_merge then 0w else rx_data_sr; (*TODO rx_data_sr *)

      wdata_shifted_byte_merge: word 32 = wdata_i_byte_merge << (st.depth_byte_merge * 8);

      (* states *)
      depth_byte_merge': num = if clear_status_byte_merge then 0
                                else if load_data_byte_merge then st.depth_byte_merge + 1
                                else st.depth_byte_merge;

      data_byte_merge': word 32 = if clear_data_byte_merge then 0
                                  else load_data_byte_merge then (wdata_shifted_byte_merge || n2w st.data_byte_merge) (*this has a small potential issue see 110:prim_packer_fifo.sv the *)
                                  else st.data_byte_merge;

      (* byte_merge outs *)
      byte_ready_byte_merge = wready_byte_merge;
      byte_ready_o_byte_merge: bool = byte_ready_byte_merge ∧ ¬do_fill_byte_merge;
      byte_valid_o_byte_merge: bool = rvalid_byte_merge;
      word_data_o_byte_mrege = st.depth_byte_merge;

      (* Shift register *)
      rd_ready_o: bool = ¬st.rx_buf_valid ∨ (st.rx_buf_valid ∧ rx_ready_sr);
      wr_ready_o: bool = tx_valid_sr;
      rd_en_i: bool = F; (* TODO uses data from FSM need to get things around right way
                            FSM can depend on values from sr *)
      rx_valid_o: bool = st.rx_buf_valid;
      rx_buf_valid': bool = if sw_rst_i then F
                            else if (rd_en_i ∧ rd_ready_o) then T
                            else if (rx_valid_o ∧ rx_ready_sr) then F
                            else st.rx_buf_valid;
    in
      <|
        fnums := fnums';
        buffered_notif := NONE;
        regs := st.regs;
        counter := counter';
        fsm_state := fsm_state';
        new_command := new_command';
        switch_required := switch_required';
        last_bit := last_bit';
        last_byte := last_byte';
        csaat := csaat';
        csid := csid';
        csid_q := csid_q';
        stall := stall';
        cmd_wr_en := cmd_wr_en';
        cmd_len := cmd_len';
        bit_counter := bit_counter';
        byte_counter := byte_counter';
        byte_ending := byte_ending';
        rx_buf_valid := rx_buf_valid';
        depth_byte_sel := depth_byte_sel';
        data_pos_byte_sel := data_pos_byte_sel';
        data_byte_sel := data_byte_sel';
        clr_byte_sel := clr_byte_sel';
      |>
End

Theorem spi_host_tick_buffered_notif_NONE:
  (spi_host_tick notif st).buffered_notif = NONE
Proof
  simp [spi_host_tick_def]
QED

Theorem spi_host_tick_unused_fnums:
  ?n. !fnums. (!i. i < n ==> fnums i = st.fnums i) ==>
  spi_host_tick notif (st with fnums := fnums) = spi_host_tick notif st with fnums := (\i. fnums (i + n))
Proof
  qexists `2`
  >> simp [spi_host_tick_def, SF ETA_ss]
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
