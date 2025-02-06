open HolKernel Parse boolLib bossLib;
open alignmentTheory;
open ffiTheory;
open i2cCoreTheory;

val _ = new_theory("i2cMappings");

Definition i2c_read_def:
  i2c_read (st: i2c_state) (nb: num) (offset: num) = case offset of
    0x0 => INR (NONE, (w2w st.regs.intr_state.fmt_threshold << 0) || (w2w st.regs.intr_state.rx_threshold << 1) || (w2w st.regs.intr_state.fmt_overflow << 2) || (w2w st.regs.intr_state.rx_overflow << 3) || (w2w st.regs.intr_state.nak << 4) || (w2w st.regs.intr_state.scl_interference << 5) || (w2w st.regs.intr_state.sda_interference << 6) || (w2w st.regs.intr_state.stretch_timeout << 7) || (w2w st.regs.intr_state.sda_unstable << 8) || (w2w st.regs.intr_state.cmd_complete << 9) || (w2w st.regs.intr_state.tx_stretch << 10) || (w2w st.regs.intr_state.tx_overflow << 11) || (w2w st.regs.intr_state.acq_full << 12) || (w2w st.regs.intr_state.unexp_stop << 13) || (w2w st.regs.intr_state.host_timeout << 14) : word32)
  | 0x4 => INR (NONE, (w2w st.regs.intr_enable.fmt_threshold << 0) || (w2w st.regs.intr_enable.rx_threshold << 1) || (w2w st.regs.intr_enable.fmt_overflow << 2) || (w2w st.regs.intr_enable.rx_overflow << 3) || (w2w st.regs.intr_enable.nak << 4) || (w2w st.regs.intr_enable.scl_interference << 5) || (w2w st.regs.intr_enable.sda_interference << 6) || (w2w st.regs.intr_enable.stretch_timeout << 7) || (w2w st.regs.intr_enable.sda_unstable << 8) || (w2w st.regs.intr_enable.cmd_complete << 9) || (w2w st.regs.intr_enable.tx_stretch << 10) || (w2w st.regs.intr_enable.tx_overflow << 11) || (w2w st.regs.intr_enable.acq_full << 12) || (w2w st.regs.intr_enable.unexp_stop << 13) || (w2w st.regs.intr_enable.host_timeout << 14) : word32)
  | 0x8 => INR (NONE, 0w : word32)
  | 0xc => INR (NONE, 0w : word32)
  | 0x10 => INR (NONE, (w2w st.regs.ctrl.enablehost << 0) || (w2w st.regs.ctrl.enabletarget << 1) || (w2w st.regs.ctrl.llpbk << 2) : word32)
  | 0x14 => INR (NONE, (w2w (i2c_get_status_fmtfull st) << 0) || (w2w (i2c_get_status_rxfull st) << 1) || (w2w (i2c_get_status_fmtempty st) << 2) || (w2w (i2c_get_status_hostidle st) << 3) || (w2w (i2c_get_status_targetidle st) << 4) || (w2w (i2c_get_status_rxempty st) << 5) || (w2w (i2c_get_status_txfull st) << 6) || (w2w (i2c_get_status_acqfull st) << 7) || (w2w (i2c_get_status_txempty st) << 8) || (w2w (i2c_get_status_acqempty st) << 9) : word32)
  | 0x18 => INR (SOME (Read rdata_read), (w2w (i2c_get_rdata_rdata st) << 0) : word32)
  | 0x1c => INR (NONE, 0w : word32)
  | 0x20 => INR (NONE, (w2w st.regs.fifo_ctrl.rxilvl << 2) || (w2w st.regs.fifo_ctrl.fmtilvl << 5) : word32)
  | 0x24 => INR (NONE, (w2w (i2c_get_fifo_status_fmtlvl st) << 0) || (w2w (i2c_get_fifo_status_txlvl st) << 8) || (w2w (i2c_get_fifo_status_rxlvl st) << 16) || (w2w (i2c_get_fifo_status_acqlvl st) << 24) : word32)
  | 0x28 => INR (NONE, (w2w st.regs.ovrd.txovrden << 0) || (w2w st.regs.ovrd.sclval << 1) || (w2w st.regs.ovrd.sdaval << 2) : word32)
  | 0x2c => INR (NONE, (w2w (i2c_get_val_scl_rx st) << 0) || (w2w (i2c_get_val_sda_rx st) << 16) : word32)
  | 0x30 => INR (NONE, (w2w st.regs.timing0.thigh << 0) || (w2w st.regs.timing0.tlow << 16) : word32)
  | 0x34 => INR (NONE, (w2w st.regs.timing1.t_r << 0) || (w2w st.regs.timing1.t_f << 16) : word32)
  | 0x38 => INR (NONE, (w2w st.regs.timing2.tsu_sta << 0) || (w2w st.regs.timing2.thd_sta << 16) : word32)
  | 0x3c => INR (NONE, (w2w st.regs.timing3.tsu_dat << 0) || (w2w st.regs.timing3.thd_dat << 16) : word32)
  | 0x40 => INR (NONE, (w2w st.regs.timing4.tsu_sto << 0) || (w2w st.regs.timing4.t_buf << 16) : word32)
  | 0x44 => INR (NONE, (w2w st.regs.timeout_ctrl.val << 0) || (w2w st.regs.timeout_ctrl.en << 31) : word32)
  | 0x48 => INR (NONE, (w2w st.regs.target_id.address0 << 0) || (w2w st.regs.target_id.mask0 << 7) || (w2w st.regs.target_id.address1 << 14) || (w2w st.regs.target_id.mask1 << 21) : word32)
  | 0x4c => INR (SOME (Read acqdata_read), (w2w (i2c_get_acqdata_abyte st) << 0) || (w2w (i2c_get_acqdata_signal st) << 8) : word32)
  | 0x50 => INR (NONE, 0w : word32)
  | 0x54 => INR (NONE, (w2w st.regs.host_timeout_ctrl.host_timeout_ctrl << 0) : word32)
  | _ => INL FFI_failed
End

Definition i2c_write_def:
  i2c_write (st: i2c_state) (nb: num) (offset: num) (value: word32) = case offset of
    0x0 =>
      let
        new_value = <|
          fmt_threshold := st.regs.intr_state.fmt_threshold && ~(w2w ((0 -- 0) value));
          rx_threshold := st.regs.intr_state.rx_threshold && ~(w2w ((1 -- 1) value));
          fmt_overflow := st.regs.intr_state.fmt_overflow && ~(w2w ((2 -- 2) value));
          rx_overflow := st.regs.intr_state.rx_overflow && ~(w2w ((3 -- 3) value));
          nak := st.regs.intr_state.nak && ~(w2w ((4 -- 4) value));
          scl_interference := st.regs.intr_state.scl_interference && ~(w2w ((5 -- 5) value));
          sda_interference := st.regs.intr_state.sda_interference && ~(w2w ((6 -- 6) value));
          stretch_timeout := st.regs.intr_state.stretch_timeout && ~(w2w ((7 -- 7) value));
          sda_unstable := st.regs.intr_state.sda_unstable && ~(w2w ((8 -- 8) value));
          cmd_complete := st.regs.intr_state.cmd_complete && ~(w2w ((9 -- 9) value));
          tx_stretch := st.regs.intr_state.tx_stretch && ~(w2w ((10 -- 10) value));
          tx_overflow := st.regs.intr_state.tx_overflow && ~(w2w ((11 -- 11) value));
          acq_full := st.regs.intr_state.acq_full && ~(w2w ((12 -- 12) value));
          unexp_stop := st.regs.intr_state.unexp_stop && ~(w2w ((13 -- 13) value));
          host_timeout := st.regs.intr_state.host_timeout && ~(w2w ((14 -- 14) value));
        |>;
        st_upd = \st'. st' with <|
          regs := st'.regs with intr_state := new_value;
          buffered_notif := NONE;
        |>;
      in
        if nb >= 2 then INR (st_upd, NONE) else INL FFI_failed
  | 0x4 =>
      let
        new_value = <|
          fmt_threshold := w2w ((0 -- 0) value);
          rx_threshold := w2w ((1 -- 1) value);
          fmt_overflow := w2w ((2 -- 2) value);
          rx_overflow := w2w ((3 -- 3) value);
          nak := w2w ((4 -- 4) value);
          scl_interference := w2w ((5 -- 5) value);
          sda_interference := w2w ((6 -- 6) value);
          stretch_timeout := w2w ((7 -- 7) value);
          sda_unstable := w2w ((8 -- 8) value);
          cmd_complete := w2w ((9 -- 9) value);
          tx_stretch := w2w ((10 -- 10) value);
          tx_overflow := w2w ((11 -- 11) value);
          acq_full := w2w ((12 -- 12) value);
          unexp_stop := w2w ((13 -- 13) value);
          host_timeout := w2w ((14 -- 14) value);
        |>;
        st_upd = \st'. st' with <|
          regs := st'.regs with intr_enable := new_value;
          buffered_notif := NONE;
        |>;
      in
        if nb >= 2 then INR (st_upd, NONE) else INL FFI_failed
  | 0x8 =>
      let
        new_value = <|
          fmt_threshold := w2w ((0 -- 0) value);
          rx_threshold := w2w ((1 -- 1) value);
          fmt_overflow := w2w ((2 -- 2) value);
          rx_overflow := w2w ((3 -- 3) value);
          nak := w2w ((4 -- 4) value);
          scl_interference := w2w ((5 -- 5) value);
          sda_interference := w2w ((6 -- 6) value);
          stretch_timeout := w2w ((7 -- 7) value);
          sda_unstable := w2w ((8 -- 8) value);
          cmd_complete := w2w ((9 -- 9) value);
          tx_stretch := w2w ((10 -- 10) value);
          tx_overflow := w2w ((11 -- 11) value);
          acq_full := w2w ((12 -- 12) value);
          unexp_stop := w2w ((13 -- 13) value);
          host_timeout := w2w ((14 -- 14) value);
        |>;
        st_upd = \st'. st';
      in
        if nb >= 2 then INR (st_upd, SOME (Write (intr_test_write new_value))) else INL FFI_failed
  | 0xc =>
      let
        new_value = <|
          fatal_fault := w2w ((0 -- 0) value);
        |>;
        st_upd = \st'. st';
      in
        if nb >= 1 then INR (st_upd, SOME (Write (alert_test_write new_value))) else INL FFI_failed
  | 0x10 =>
      let
        new_value = <|
          enablehost := w2w ((0 -- 0) value);
          enabletarget := w2w ((1 -- 1) value);
          llpbk := w2w ((2 -- 2) value);
        |>;
        st_upd = \st'. st' with <|
          regs := st'.regs with ctrl := new_value;
          buffered_notif := NONE;
        |>;
      in
        if nb >= 1 then INR (st_upd, NONE) else INL FFI_failed
  | 0x14 =>
      let
        st_upd = \st'. st';
      in
        if nb >= 2 then INR (st_upd, NONE) else INL FFI_failed
  | 0x18 =>
      let
        st_upd = \st'. st';
      in
        if nb >= 1 then INR (st_upd, NONE) else INL FFI_failed
  | 0x1c =>
      let
        new_value = <|
          fbyte := w2w ((7 -- 0) value);
          start := w2w ((8 -- 8) value);
          stop := w2w ((9 -- 9) value);
          read := w2w ((10 -- 10) value);
          rcont := w2w ((11 -- 11) value);
          nakok := w2w ((12 -- 12) value);
        |>;
        st_upd = \st'. st' with <|
          regs := st'.regs with fdata := new_value;
          buffered_notif := SOME fdata_write;
        |>;
      in
        if nb >= 2 then INR (st_upd, NONE) else INL FFI_failed
  | 0x20 =>
      let
        new_value = <|
          rxrst := w2w ((0 -- 0) value);
          fmtrst := w2w ((1 -- 1) value);
          rxilvl := w2w ((4 -- 2) value);
          fmtilvl := w2w ((6 -- 5) value);
          acqrst := w2w ((7 -- 7) value);
          txrst := w2w ((8 -- 8) value);
        |>;
        st_upd = \st'. st' with <|
          regs := st'.regs with fifo_ctrl := new_value;
          buffered_notif := SOME fifo_ctrl_write;
        |>;
      in
        if nb >= 2 then INR (st_upd, NONE) else INL FFI_failed
  | 0x24 =>
      let
        st_upd = \st'. st';
      in
        if nb >= 4 then INR (st_upd, NONE) else INL FFI_failed
  | 0x28 =>
      let
        new_value = <|
          txovrden := w2w ((0 -- 0) value);
          sclval := w2w ((1 -- 1) value);
          sdaval := w2w ((2 -- 2) value);
        |>;
        st_upd = \st'. st' with <|
          regs := st'.regs with ovrd := new_value;
          buffered_notif := NONE;
        |>;
      in
        if nb >= 1 then INR (st_upd, NONE) else INL FFI_failed
  | 0x2c =>
      let
        st_upd = \st'. st';
      in
        if nb >= 4 then INR (st_upd, NONE) else INL FFI_failed
  | 0x30 =>
      let
        new_value = <|
          thigh := w2w ((15 -- 0) value);
          tlow := w2w ((31 -- 16) value);
        |>;
        st_upd = \st'. st' with <|
          regs := st'.regs with timing0 := new_value;
          buffered_notif := NONE;
        |>;
      in
        if nb >= 4 then INR (st_upd, NONE) else INL FFI_failed
  | 0x34 =>
      let
        new_value = <|
          t_r := w2w ((15 -- 0) value);
          t_f := w2w ((31 -- 16) value);
        |>;
        st_upd = \st'. st' with <|
          regs := st'.regs with timing1 := new_value;
          buffered_notif := NONE;
        |>;
      in
        if nb >= 4 then INR (st_upd, NONE) else INL FFI_failed
  | 0x38 =>
      let
        new_value = <|
          tsu_sta := w2w ((15 -- 0) value);
          thd_sta := w2w ((31 -- 16) value);
        |>;
        st_upd = \st'. st' with <|
          regs := st'.regs with timing2 := new_value;
          buffered_notif := NONE;
        |>;
      in
        if nb >= 4 then INR (st_upd, NONE) else INL FFI_failed
  | 0x3c =>
      let
        new_value = <|
          tsu_dat := w2w ((15 -- 0) value);
          thd_dat := w2w ((31 -- 16) value);
        |>;
        st_upd = \st'. st' with <|
          regs := st'.regs with timing3 := new_value;
          buffered_notif := NONE;
        |>;
      in
        if nb >= 4 then INR (st_upd, NONE) else INL FFI_failed
  | 0x40 =>
      let
        new_value = <|
          tsu_sto := w2w ((15 -- 0) value);
          t_buf := w2w ((31 -- 16) value);
        |>;
        st_upd = \st'. st' with <|
          regs := st'.regs with timing4 := new_value;
          buffered_notif := NONE;
        |>;
      in
        if nb >= 4 then INR (st_upd, NONE) else INL FFI_failed
  | 0x44 =>
      let
        new_value = <|
          val := w2w ((30 -- 0) value);
          en := w2w ((31 -- 31) value);
        |>;
        st_upd = \st'. st' with <|
          regs := st'.regs with timeout_ctrl := new_value;
          buffered_notif := NONE;
        |>;
      in
        if nb >= 4 then INR (st_upd, NONE) else INL FFI_failed
  | 0x48 =>
      let
        new_value = <|
          address0 := w2w ((6 -- 0) value);
          mask0 := w2w ((13 -- 7) value);
          address1 := w2w ((20 -- 14) value);
          mask1 := w2w ((27 -- 21) value);
        |>;
        st_upd = \st'. st' with <|
          regs := st'.regs with target_id := new_value;
          buffered_notif := NONE;
        |>;
      in
        if nb >= 4 then INR (st_upd, NONE) else INL FFI_failed
  | 0x4c =>
      let
        st_upd = \st'. st';
      in
        if nb >= 2 then INR (st_upd, NONE) else INL FFI_failed
  | 0x50 =>
      let
        new_value = <|
          txdata := w2w ((7 -- 0) value);
        |>;
        st_upd = \st'. st' with <|
          regs := st'.regs with txdata := new_value;
          buffered_notif := SOME txdata_write;
        |>;
      in
        if nb >= 1 then INR (st_upd, NONE) else INL FFI_failed
  | 0x54 =>
      let
        new_value = <|
          host_timeout_ctrl := w2w ((31 -- 0) value);
        |>;
        st_upd = \st'. st' with <|
          regs := st'.regs with host_timeout_ctrl := new_value;
          buffered_notif := NONE;
        |>;
      in
        if nb >= 4 then INR (st_upd, NONE) else INL FFI_failed
  | _ => INL FFI_failed
End

Definition i2c_addrs_def:
  (* TODO: I think sh_memaddrs is supposed to only contain word-aligned addresses (which is, rather counterintuitively, what byte_align does), but we should double-check. *)
  i2c_addrs = {byte_align 0x0w; byte_align 0x4w; byte_align 0x8w; byte_align 0xcw; byte_align 0x10w; byte_align 0x14w; byte_align 0x18w; byte_align 0x1cw; byte_align 0x20w; byte_align 0x24w; byte_align 0x28w; byte_align 0x2cw; byte_align 0x30w; byte_align 0x34w; byte_align 0x38w; byte_align 0x3cw; byte_align 0x40w; byte_align 0x44w; byte_align 0x48w; byte_align 0x4cw; byte_align 0x50w; byte_align 0x54w}
End

val _ = export_theory();
