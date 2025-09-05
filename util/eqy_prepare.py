# Takes in the version of `i2c_reg_top` spat out by the translator (that is, the
# one which has the input/output signals of `i2c` but only contains the `always`
# blocks of `i2c_reg_top`), and converts it into a version with the same
# interface as the real `i2c_reg_top` (minus `devmode_i`).

import re
import sys

from .common import block, ip, name, windows

with open(sys.argv[2]) as f:
    input = f.read()

reg_re = "|".join(name(reg) for reg in block.registers if not reg.is_homogeneous())
field_re = "|".join(name(field) for reg in block.registers for field in reg.fields)
input = re.sub(
    rf"(reg2hw|hw2reg)_({reg_re})_({field_re})_(d|de|q|qe|re)", r"\1.\2.\3.\4", input
)

homo_reg_re = "|".join(name(reg) for reg in block.registers if reg.is_homogeneous())
input = re.sub(
    rf"(reg2hw|hw2reg)_({homo_reg_re})_({field_re})_(d|de|q|qe|re)", r"\1.\2.\4", input
)

multireg_re = "|".join(name(reg) for reg in block.multiregs if not reg.is_homogeneous())
multireg_field_re = "|".join(
    name(field) for reg in block.multiregs for field in reg.reg.fields
)
input = re.sub(
    rf"(reg2hw|hw2reg)_({multireg_re})_(\d*)_({multireg_field_re})_\d*_(d|de|q|qe|re)",
    r"\1.\2[\3].\4.\5",
    input,
)

homomultireg_re = "|".join(name(reg) for reg in block.multiregs if reg.is_homogeneous())
input = re.sub(
    rf"(reg2hw|hw2reg)_({multireg_re})_(\d*)_({multireg_field_re})_\d*_(d|de|q|qe|re)",
    r"\1.\2[\3].\5",
    input,
)

for i, window in enumerate(windows):
    input = re.sub(
        rf"win_buses_req_{name(window)}_(addr|write|wdata|wstrb|valid)",
        rf"reg_req_win_o[{i}].\1",
        input,
    )
    input = re.sub(
        rf"win_buses_rsp_{name(window)}_(rdata|error|ready)",
        rf"reg_rsp_win_i[{i}].\1",
        input,
    )

input = re.sub(r"logic.*(reg2hw|hw2reg|reg_req_win|reg_rsp_win).*;\n", "", input)

if len(windows) > 0:
    window_ports = f"""
  output reg_req_t[{len(windows) - 1}:0] reg_req_win_o,
  input reg_rsp_t[{len(windows) - 1}:0] reg_rsp_win_i,"""
else:
    window_ports = ""

input = re.sub(
    rf"module {ip.name}_circuit\([^)]*\)",
    f"""\
typedef struct packed {{
  logic [47:0] addr;
  logic write;
  logic [31:0] wdata;
  logic [3:0] wstrb;
  logic valid;
}} reg_req_t;

typedef struct packed {{
  logic [31:0] rdata;
  logic error;
  logic ready;
}} reg_rsp_t;

module {ip.name}_reg_top_wrapper(
  input logic clk_i,
  input logic rst_ni,
  input logic[85:0] reg_req_i,
  output logic[33:0] reg_rsp_o,{window_ports}
  output {ip.name}_reg_pkg::{ip.name}_reg2hw_t reg2hw,
  input {ip.name}_reg_pkg::{ip.name}_hw2reg_t hw2reg
)""",
    input,
)

with open(sys.argv[3], "w") as f:
    f.write(input)
