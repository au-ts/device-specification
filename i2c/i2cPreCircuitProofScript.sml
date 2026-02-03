Theory i2cPreCircuitProof
Ancestors i2cCircuitState i2cCore i2cMappings i2cRegsComm

Definition encode_fsm_def:
  encode_fsm (machine: fsmState) =
  case machine of
    Idle => idle
  | Active => active
  | Transmitting ClockLow => clockLow
  | Transmitting ClockPulse => clockPulse
  | Transmitting HoldBit => holdBit
  | Transmitting ClockLowAck => clockLowAck
  | Transmitting ClockPulseAck => clockPulseAck
  | Transmitting HoldDevAck => holdDevAck
  | Receiving ReadClockLow => readClockLow
  | Receiving ReadClockPulse => readClockPulse
  | Receiving ReadHoldBit => readHoldBit
  | Receiving HostClockLowAck => hostClockLowAck
  | Receiving HostClockPulseAck => hostClockPulseAck
  | Receiving HostHoldBitAck => hostHoldBitAck
  | Starting SetupStart => setupStart
  | Starting HoldStart => holdStart
  | Starting ClockStart => clockStart
  | Stopping ClockStop => clockStop
  | Stopping SetupStop => setupStop
  | Stopping HoldStop => holdStop
  | PopFmtFifo => popFmtFifo
End

Definition fifo_rel_def:
  (fifo_rel [] (circuit : 'a word -> 'b) (rptr : 'c word) wptr ⇔ rptr = wptr)
∧ (fifo_rel (w :: ws) circuit rptr wptr ⇔
     ((word_bit (dimindex(:'c) - 1) rptr = word_bit (dimindex(:'c) - 1) wptr) ⇒ wptr >+ rptr)
   ∧ ((word_bit (dimindex(:'c) - 1) rptr ≠ word_bit (dimindex(:'c) - 1) wptr) ⇒
      ((dimindex(:'a) - 1 >< 0) wptr : 'a word) <=+ ((dimindex(:'a) - 1 >< 0) rptr :'a word))
   ∧ (circuit $ ((dimindex(:'a) - 1 >< 0) rptr : 'a word) = w)
   ∧ fifo_rel ws circuit (rptr + 1w) wptr)
End

Definition core_sim_rel_def:
  core_sim_rel (machine : i2c_state) (circuit: i2c_circuit_state) =
  ( fifo_rel machine.rx_fifo circuit.rx_fifo_regfile circuit.rx_fifo.rptr circuit.rx_fifo.wptr
  ∧ fifo_rel machine.fmt_fifo circuit.fmt_fifo_regfile circuit.fmt_fifo.rptr circuit.fmt_fifo.wptr
  ∧ circuit.tx_fifo.rptr = circuit.tx_fifo.wptr
  ∧ circuit.acq_fifo.rptr = circuit.acq_fifo.wptr
  ∧ encode_fsm (machine.fsm_state) = circuit.fsm_state
  ∧ machine.counter = circuit.counter
  ∧ machine.pend_restart = circuit.pend_restart
  ∧ machine.trans_started = circuit.trans_started
  ∧ machine.bit_index = circuit.bit_index
  ∧ machine.stretch_idle_cnt = circuit.stretch_idle_cnt
  ∧ machine.byte_index = circuit.byte_index
  ∧ machine.read_byte = circuit.read_byte
  ∧ machine.scl_rx_val = circuit.scl_rx_val
  ∧ machine.sda_rx_val = circuit.sda_rx_val
  ∧ machine.regs = circuit.regs
  ∧ machine.under_rst = circuit.under_rst
  ∧ machine.scl_buf = circuit.scl_buf
  ∧ machine.sda_buf = circuit.sda_buf
  ∧ machine.scl_sync = circuit.scl_sync
  ∧ machine.sda_sync = circuit.sda_sync
  )
End

Definition i2c_core_state_rel_def:
  (* mstate = model state, cstate = circuit state *)
  i2c_core_state_rel (mstate: i2c_state) (cstate: i2c_circuit_state) <=> core_sim_rel mstate cstate
End

Definition i2c_state_rel_def:
  i2c_state_rel (mstate: i2c_state) (cstate: i2c_circuit_state) <=>
    mstate.regs = cstate.regs /\
    i2c_notif_rel mstate.buffered_notif cstate.reg2hw /\
    i2c_core_state_rel mstate cstate
End

Theorem i2c_state_rel_fnums:
  i2c_state_rel (st with fnums := fnums) = i2c_state_rel st
Proof
  irule EQ_EXT
  >> simp [i2c_state_rel_def, i2c_notif_rel_def, i2c_core_state_rel_def, i2c_hwext_read_rel_def, i2c_win_read_rel_def, core_sim_rel_def]
  >> simp [i2c_get_status_fmtfull_def, i2c_get_status_rxfull_def, i2c_get_status_fmtempty_def, i2c_get_status_hostidle_def, i2c_get_status_targetidle_def, i2c_get_status_rxempty_def, i2c_get_status_txfull_def, i2c_get_status_acqfull_def, i2c_get_status_txempty_def, i2c_get_status_acqempty_def, i2c_get_rdata_rdata_def, i2c_get_fifo_status_fmtlvl_def, i2c_get_fifo_status_txlvl_def, i2c_get_fifo_status_rxlvl_def, i2c_get_fifo_status_acqlvl_def, i2c_get_val_scl_rx_def, i2c_get_val_sda_rx_def, i2c_get_acqdata_abyte_def, i2c_get_acqdata_signal_def]
QED