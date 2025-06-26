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

module spi_host_reg_top_wrapper (
    input logic clk_i,
    input logic rst_ni,
    input logic [85:0] reg_req_i,
    output logic [33:0] reg_rsp_o,
    output spi_host_reg_pkg::spi_host_reg2hw_t reg2hw,
    input spi_host_reg_pkg::spi_host_hw2reg_t hw2reg
);
  spi_host_reg_top #(
      .reg_req_t(reg_req_t),
      .reg_rsp_t(reg_rsp_t)
  ) inner (
      .clk_i,
      .rst_ni,
      .reg_req_i,
      .reg_rsp_o,
      .reg2hw,
      .hw2reg,
      .devmode_i(1)
  );
endmodule
