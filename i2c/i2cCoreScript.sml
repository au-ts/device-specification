open HolKernel Parse boolLib bossLib;
open i2cRegsTheory;

val _ = new_theory("i2cCore");

Datatype:
  txState =
    ClockLow
  | ClockPulse
  | HoldBit
  | ClockLowAck
  | ClockPulseAck
  | HoldDevAck
End

Datatype:
  rxState =
   ReadClockLow
 | ReadClockPulse
 | ReadHoldBit
 | HostClockLowAck
 | HostClockPulseAck
 | HostHoldBitAck
End

Datatype:
  stopState = ClockStop | SetupStop | HoldStop
End

Datatype:
  startState = SetupStart | HoldStart | ClockStart
End

Datatype:
  fsmState =
    Idle
  | Active
  | Transmitting txState
  | Receiving rxState
  | Starting startState
  | Stopping stopState
  | PopFmtFifo
End

Datatype:
  i2c_state = <|
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
    regs : i2c_regs;
    (* Although there can only be one regbus transaction per clock cycle, because
     * non-`hwext` transactions only issue notifications on the next clock cycle,
     * whereas `hwext` transactions issue notifications immediately, you can end up
     * with two notifications on the same clock cycle if you have a non-`hwext`
     * transaction immediately followed by a `hwext` transaction. *)
    buffered_notif : i2c_notif option;

    (* Maximum length: 64 *)
    rx_fifo : word8 list;

    (* 8 byte of data + 5 byte of formatting indicators *)
    fmt_fifo : 13 word list;
    fsm_state : fsmState;
    counter : 20 word ;
    pend_restart : bool;
    trans_started : bool;
    bit_index : 3 word ;
    stretch_idle_cnt : 32 word;
    byte_index : 9 word;
    read_byte : 8 word;
    read_byte_clr: bool;
    shift_data_en: bool;
    scl_rx_val : 16 word;
    sda_rx_val : 16 word;
  |>
End


(* Stubs *)
Definition i2c_get_status_fmtfull_def:
  i2c_get_status_fmtfull (st: i2c_state) = if LENGTH st.fmt_fifo >= 64 then 1w else 0w
End

Definition i2c_get_status_rxfull_def:
  i2c_get_status_rxfull (st: i2c_state) = if LENGTH st.rx_fifo >= 64 then 1w else 0w
End

Definition i2c_get_status_fmtempty_def:
  i2c_get_status_fmtempty (st: i2c_state) = if NULL st.fmt_fifo then 1w else 0w
End

Definition i2c_get_status_hostidle_def:
  i2c_get_status_hostidle (st: i2c_state) = if (st.fsm_state = Idle) then 1w else 0w
End

Definition i2c_get_status_targetidle_def:
  i2c_get_status_targetidle (st: i2c_state) = 1w
End

Definition i2c_get_status_rxempty_def:
  i2c_get_status_rxempty (st: i2c_state) = if NULL st.rx_fifo then 1w else 0w
End

Definition i2c_get_status_txfull_def:
  i2c_get_status_txfull (st: i2c_state) = 0w
End

Definition i2c_get_status_acqfull_def:
  i2c_get_status_acqfull (st: i2c_state) = 0w
End

Definition i2c_get_status_txempty_def:
  i2c_get_status_txempty (st: i2c_state) = 0w
End

Definition i2c_get_status_acqempty_def:
  i2c_get_status_acqempty (st: i2c_state) = 0w
End

Definition i2c_get_rdata_rdata_def:
  (* `OutputZeroIfEmpty` is set to 1, so we can rely on it always being 0 in that
   * case rather than having to use `fnums`. *)
  i2c_get_rdata_rdata (st: i2c_state) = if NULL st.rx_fifo then 0w else HD st.rx_fifo
End

Definition i2c_get_fifo_status_fmtlvl_def:
  i2c_get_fifo_status_fmtlvl (st: i2c_state) = n2w $ LENGTH st.fmt_fifo
End

Definition i2c_get_fifo_status_txlvl_def:
  i2c_get_fifo_status_txlvl (st: i2c_state) = 0w
End

Definition i2c_get_fifo_status_rxlvl_def:
  i2c_get_fifo_status_rxlvl (st: i2c_state) = n2w (LENGTH st.rx_fifo)
End

Definition i2c_get_fifo_status_acqlvl_def:
  i2c_get_fifo_status_acqlvl (st: i2c_state) = 0w
End

Definition i2c_get_val_scl_rx_def:
  i2c_get_val_scl_rx (st: i2c_state) = st.scl_rx_val
End

Definition i2c_get_val_sda_rx_def:
  i2c_get_val_sda_rx (st: i2c_state) = st.sda_rx_val
End

Definition i2c_get_acqdata_abyte_def:
  i2c_get_acqdata_abyte (st: i2c_state) = 0w
End

Definition i2c_get_acqdata_signal_def:
  i2c_get_acqdata_signal (st: i2c_state) = 0w
End


Definition i2c_eat_fnum:
  i2c_eat_fnum st = (st with fnums := st.fnums o SUC, st.fnums 0)
End

Datatype:
  delay = <|
    setup_start : 20 word ;
    hold_start  : 20 word ;
    setup_data  : 20 word ;
    clock_start : 20 word ;
    clock_low   : 20 word ;
    clock_pulse : 20 word ;
    hold_bit    : 20 word ;
    clock_stop  : 20 word ;
    setup_stop  : 20 word ;
    hold_stop   : 20 word ;
  |>
End


(* Simulates one clock cycle of the I2C core.
 *
 * Register reads/writes are handled externally, with new values simply being
 * made available in `st`. If the hardware has a `qe`/`re` signal to detect
 * interactions with a register, a notification is provided that that's occured.
 * For regular registers, this occurs on the clock cycle after the I/O actually
 * occurs, but for `hwext` registers it occurs on the same clock cycle. *)
Definition i2c_tick_def:
  i2c_tick (hwext_notif: i2c_hwext_notif option) (st: i2c_state) =
    let
      fnums = st.fnums;
      fmt_fifo' = if st.buffered_notif = SOME fdata_write ∧ LENGTH st.fmt_fifo < 64
                  then flip SNOC st.fmt_fifo
                               $  w2w st.regs.fdata.fbyte
                               || w2w ( st.regs.fdata.start << 8  )
                               || w2w ( st.regs.fdata.stop  << 9  )
                               || w2w ( st.regs.fdata.read  << 10 )
                               || w2w ( st.regs.fdata.rcont << 11 )
                               || w2w ( st.regs.fdata.nakok << 12 )
                  else st.fmt_fifo;
      fmt_fifo'' = if st.fsm_state = PopFmtFifo then TL fmt_fifo' else fmt_fifo';

      delay = <|
                 setup_start := (w2w st.regs.timing1.t_r : 20 word) + w2w st.regs.timing2.tsu_sta ;
                 hold_start  := (w2w st.regs.timing1.t_f : 20 word) + w2w st.regs.timing2.thd_sta ;
                 setup_data  := (w2w st.regs.timing1.t_r : 20 word) + w2w st.regs.timing3.tsu_dat ;
                 clock_start :=  w2w st.regs.timing3.thd_dat ;
                 clock_low   := (w2w st.regs.timing0.tlow : 20 word) - w2w st.regs.timing3.thd_dat ;
                 clock_pulse := (w2w st.regs.timing1.t_r : 20 word) + w2w st.regs.timing0.thigh + w2w st.regs.timing1.t_f ;
                 hold_bit    := (w2w st.regs.timing1.t_f : 20 word) + w2w st.regs.timing3.thd_dat ;
                 clock_stop  := (w2w st.regs.timing1.t_f : 20 word) + w2w st.regs.timing0.tlow - w2w st.regs.timing3.thd_dat ;
                 setup_stop  := (w2w st.regs.timing1.t_r : 20 word) + w2w st.regs.timing4.tsu_sto ;
                 hold_stop   := (w2w st.regs.timing1.t_r : 20 word) + w2w st.regs.timing4.t_buf - w2w st.regs.timing2.tsu_sta ;
              |>;
      curr_delay = case st.fsm_state of
                     Receiving ReadClockLow      => delay.clock_low
                   | Receiving ReadClockPulse    => delay.clock_pulse
                   | Receiving ReadHoldBit       => delay.hold_bit
                   | Receiving HostClockLowAck   => delay.clock_low
                   | Receiving HostClockPulseAck => delay.clock_pulse
                   | Receiving HostHoldBitAck    => delay.hold_bit
                   | Stopping ClockStop          => delay.clock_stop
                   | Stopping SetupStop          => delay.setup_stop
                   | Stopping HoldStop           => delay.hold_stop
                   | Starting SetupStart         => delay.setup_start
                   | Starting HoldStart          => delay.hold_start
                   | Starting ClockStart         => delay.clock_start
                   | Transmitting ClockLow       => delay.clock_low
                   | Transmitting ClockPulse     => delay.clock_pulse
                   | Transmitting HoldBit        => delay.hold_bit
                   | Transmitting ClockLowAck    => delay.clock_low
                   | Transmitting ClockPulseAck  => delay.clock_pulse
                   | Transmitting HoldDevAck     => delay.hold_bit
                   | _                           => 0w ;

      load_tcount = (st.fsm_state ≠ Idle ∧ st.counter = 1w ∨ st.fsm_state = PopFmtFifo);
      log_start = (st.fsm_state = Starting SetupStart ∧ st.counter = 1w);
      log_stop  = (st.fsm_state = Stopping ClockStop ∧ st.counter = 1w);

      fmt_flag_start_before = (¬ NULL st.fmt_fifo ∧ word_bit 8 $ HD st.fmt_fifo);
      fmt_flag_stop_after   = (¬ NULL st.fmt_fifo ∧ word_bit 9  $ HD st.fmt_fifo);
      fmt_flag_read_bytes   = (¬ NULL st.fmt_fifo ∧ word_bit 10 $ HD st.fmt_fifo);
      fmt_byte : 8 word     = if ¬ NULL st.fmt_fifo then (7 >< 0) (HD st.fmt_fifo) else 0w;

      req_restart = (¬fmt_flag_read_bytes
                    ∧ fmt_flag_start_before
                    ∧ st.fsm_state = Active
                    ∧ st.trans_started
                    );

      bit_clr = ((st.fsm_state = Transmitting HoldBit ∨ st.fsm_state = Receiving ReadHoldBit)
                ∧ st.counter = 1w ∧ st.bit_index = 0w);

      bit_decr = ((st.fsm_state = Transmitting HoldBit ∨ st.fsm_state = Receiving ReadHoldBit)
                 ∧ st.counter = 1w ∧ st.bit_index ≠ 0w);

      stretch_en = ( st.fsm_state = Transmitting ClockPulse
                   ∨ st.fsm_state = Transmitting ClockPulseAck
                   ∨ st.fsm_state = Receiving ReadClockPulse
                   ∨ st.fsm_state = Receiving HostClockPulseAck
                   );

      scl_d = ¬( st.fsm_state = Starting ClockStart
               ∨ st.fsm_state = Transmitting ClockLow
               ∨ st.fsm_state = Transmitting HoldBit
               ∨ st.fsm_state = Transmitting ClockLowAck
               ∨ st.fsm_state = Transmitting HoldDevAck
               ∨ st.fsm_state = Receiving ReadClockLow
               ∨ st.fsm_state = Receiving ReadHoldBit
               ∨ st.fsm_state = Receiving HostClockLowAck
               ∨ st.fsm_state = Receiving HostHoldBitAck
               ∨ st.fsm_state = Receiving HostHoldBitAck
               ∨ st.fsm_state = Stopping ClockStop
               ∨ st.fsm_state = Active ∧ ¬fmt_flag_start_before
               ∨ st.fsm_state = Active ∧ st.trans_started
               ∨ st.fsm_state = PopFmtFifo ∧ ¬fmt_flag_stop_after
               );

      scl_i : 1 word = n2w $ fnums 0;
      scl_rx_val' : 16 word = ((14 >< 0) st.scl_rx_val : 15 word) @@ scl_i;
      stretch_idle_cnt' = if stretch_en ∧ scl_d ∧ ¬(word_bit 0 scl_i) then st.stretch_idle_cnt + 1w else 0w;
      counter' = if load_tcount then curr_delay
                 else if st.stretch_idle_cnt = 0w then st.counter - 1w
                 else st.counter;
      byte_clr = (st.fsm_state = Active ∧ fmt_flag_read_bytes);
      byte_decr = (st.fsm_state = Receiving HostHoldBitAck ∧ st.counter = 1w ∧ st.byte_index ≠ 1w);
      byte_num = if ¬fmt_flag_read_bytes then (0w : 9 word)
                 else if fmt_byte = 0w then (256w : 9 word)
                 else w2w fmt_byte;

      byte_index' = if byte_clr then byte_num
                    else if byte_decr then st.byte_index - 1w
                    else st.byte_index;
      fsm_state' = case st.fsm_state of
                     Idle              => if st.regs.ctrl.enablehost = 1w ∧ ¬ NULL st.fmt_fifo then Active
                                          else Idle

                   | Active            => if word_bit 10 $ HD st.fmt_fifo then Receiving ReadClockLow
                                          else if fmt_flag_start_before ∧ ¬st.trans_started then Starting SetupStart
                                          else Transmitting ClockLow

                   | Receiving
                     ReadClockLow      => if st.counter > 1w then Receiving ReadClockLow
                                          else Receiving ReadClockPulse

                   | Receiving
                     ReadClockPulse    => if st.counter > 1w then Receiving ReadClockPulse
                                          else Receiving ReadHoldBit

                   | Receiving
                     ReadHoldBit       => if st.counter > 1w then Receiving ReadHoldBit
                                          else Receiving HostClockLowAck

                   | Receiving
                     HostClockLowAck   => if st.counter > 1w then Receiving HostClockLowAck
                                         else Receiving HostClockPulseAck

                   | Receiving
                     HostClockPulseAck => if st.counter > 1w then Receiving HostClockPulseAck
                                          else Receiving HostHoldBitAck

                   | Receiving
                     HostHoldBitAck    => if st.counter > 1w then Receiving HostHoldBitAck
                                          else if st.byte_index = 1w ∧ fmt_flag_stop_after then Stopping ClockStop
                                          else if st.byte_index = 1w ∧ ¬fmt_flag_stop_after  then PopFmtFifo
                                          else Receiving ReadClockLow

                   | Stopping
                     ClockStop         => if st.counter > 1w then Stopping ClockStop
                                          else Stopping SetupStop

                   | Stopping
                     SetupStop         => if st.counter > 1w then Stopping SetupStop
                                          else Stopping HoldStop

                   | Stopping
                     HoldStop          => if st.counter > 1w then Stopping HoldStop
                                          else if st.regs.ctrl.enablehost = 0w then Idle
                                          else PopFmtFifo

                   | Starting
                     SetupStart        => if st.counter > 1w then Starting SetupStart
                                          else Starting HoldStart

                   | Starting
                     HoldStart         => if st.counter > 1w then Starting HoldStart
                                          else Starting ClockStart

                   | Starting
                     ClockStart        => if st.counter > 1w then Starting ClockStart
                                          else Transmitting ClockLow

                   | Transmitting
                     ClockLow          => if st.counter > 1w then Transmitting ClockLow
                                          else if st.pend_restart then Starting SetupStart
                                          else Transmitting ClockPulse

                   | Transmitting
                     ClockPulse        => if st.counter > 1w then Transmitting ClockPulse
                                          else Transmitting HoldBit

                   | Transmitting
                     HoldBit           => if st.counter > 1w then Transmitting HoldBit
                                          else if st.bit_index = 0w then Transmitting ClockLowAck
                                          else Transmitting ClockLow

                   | Transmitting
                     ClockLowAck       => if st.counter > 1w then Transmitting ClockLowAck else Transmitting ClockPulseAck

                   | Transmitting
                     ClockPulseAck     => if st.counter > 1w then Transmitting ClockPulseAck else Transmitting HoldDevAck

                   | Transmitting
                     HoldDevAck        => if st.counter > 1w then Transmitting HoldDevAck
                                          else if word_bit 9 $ HD st.fmt_fifo then Stopping ClockStop
                                          else PopFmtFifo

                   | PopFmtFifo        => if st.regs.ctrl.enablehost = 0w then Stopping ClockStop
                                          else if NULL st.fmt_fifo then Idle
                                          else Active;
      read_byte_clr' = ( st.fsm_state = Receiving ReadHoldBit ∧ st.counter = 1w ∧ st.bit_index = 0w );
      shift_data_en' = ( st.fsm_state = Receiving ReadClockPulse ∧ st.counter = 1w ) ;
      (* fnums 1 used to indicate sda_i *)
      sda_i : 1 word = n2w $ fnums 1;
      sda_rx_val' : 16 word = ((14 >< 0) st.sda_rx_val : 15 word) @@ sda_i;
      read_byte' : 8 word = if read_byte_clr' then 0w
                            else if shift_data_en' then
                              ((6 >< 0) st.read_byte : 7 word) @@ sda_i
                            else
                              st.read_byte;

      (* `Pass` is set to 0, which means that a value cannot be removed from the FIFO
       * on the same clock cycle that it is inserted, and so this needs to go first so
       * that it can't see any newly-inserted values. *)
      rx_fifo' = if hwext_notif = SOME (Read rdata_read) ∧ ¬NULL st.rx_fifo then TL st.rx_fifo else st.rx_fifo;

      (* The FIFO can't insert into a spot that was freed in the same clock cycle, so
       * we need to use `st.rx_fifo` rather than `rx_fifo'`. *)
      rx_fifo'' = if st.fsm_state = Receiving ReadHoldBit ∧ fsm_state' = Receiving HostClockLowAck ∧ LENGTH st.rx_fifo < 64
                  then flip SNOC rx_fifo' $ st.read_byte else rx_fifo';

      regs' = if (st.fsm_state = Transmitting ClockPulseAck ∧ ¬ (word_bit 12 $ HD st.fmt_fifo) ∧ word_bit 0 sda_i)
              then st.regs with <| intr_state := (st.regs.intr_state with <| nak := 1w |>) |>
              else if ( st.fsm_state = Stopping HoldStop
                      ∨ st.fsm_state = Starting SetupStart ∧ log_start ∧ st.pend_restart)
              then st.regs with <| intr_state := (st.regs.intr_state with <| cmd_complete := 1w |>) |>
              else st.regs;


      pend_restart' = if st.pend_restart ∧ st.regs.ctrl.enablehost = 0w ∨ log_start then F
                      else if req_restart then T
                      else st.pend_restart;


      trans_started' = if st.trans_started ∧ st.regs.ctrl.enablehost = 0w ∨ log_stop then F
                       else if log_start then T
                       else st.trans_started;

      bit_index' = if bit_clr then 7w
                   else if bit_decr then st.bit_index - 1w
                   else st.bit_index;

      fnums' = λn. fnums (n + 2);
    in
      <|
        fnums := fnums';
        buffered_notif := NONE;
        rx_fifo := rx_fifo'';
        fmt_fifo := fmt_fifo'';
        regs := regs';
        counter := counter';
        fsm_state := fsm_state';
        pend_restart := pend_restart';
        trans_started := trans_started';
        bit_index := bit_index';
        stretch_idle_cnt := stretch_idle_cnt';
        byte_index := byte_index';
        read_byte := read_byte';
        read_byte_clr := read_byte_clr';
        shift_data_en := shift_data_en';
        scl_rx_val := scl_rx_val';
        sda_rx_val := sda_rx_val';
      |>
End



val _ = export_theory();
