typedef struct packed {
  logic [47:0] addr;
  logic write;
  logic [31:0] wdata;
  logic [3:0] wstrb;
  logic valid;
} reg_req_t;

typedef struct packed {
  logic [31:0] rdata;
  logic error;
  logic ready;
} reg_rsp_t;

module i2c_circuit (
  input logic clk_i,
  input logic rst_ni,
  input logic [85:0] reg_req_i,
  input logic cio_scl_i,
  input logic cio_sda_i,
  output logic [33:0] reg_rsp_o,
  output logic cio_scl_o,
  output logic cio_scl_en_o,
  output logic cio_sda_o,
  output logic cio_sda_en_o,
  output logic intr_fmt_threshold_o,
  output logic intr_rx_threshold_o,
  output logic intr_fmt_overflow_o,
  output logic intr_rx_overflow_o,
  output logic intr_nak_o,
  output logic intr_scl_interference_o,
  output logic intr_sda_interference_o,
  output logic intr_stretch_timeout_o,
  output logic intr_sda_unstable_o,
  output logic intr_cmd_complete_o,
  output logic intr_tx_stretch_o,
  output logic intr_tx_overflow_o,
  output logic intr_acq_full_o,
  output logic intr_unexp_stop_o,
  output logic intr_host_timeout_o
);
  i2c #(
    .reg_req_t(reg_req_t),
    .reg_rsp_t(reg_rsp_t)
  ) inner (
    .clk_i,
    .rst_ni,
    .reg_req_i,
    .cio_scl_i,
    .cio_sda_i,
    .reg_rsp_o,
    .cio_scl_o,
    .cio_scl_en_o,
    .cio_sda_o,
    .cio_sda_en_o,
    .intr_fmt_threshold_o,
    .intr_rx_threshold_o,
    .intr_fmt_overflow_o,
    .intr_rx_overflow_o,
    .intr_nak_o,
    .intr_scl_interference_o,
    .intr_sda_interference_o,
    .intr_stretch_timeout_o,
    .intr_sda_unstable_o,
    .intr_cmd_complete_o,
    .intr_tx_stretch_o,
    .intr_tx_overflow_o,
    .intr_acq_full_o,
    .intr_unexp_stop_o,
    .intr_host_timeout_o
  );
endmodule
