# Takes in the version of `i2c_reg_top` spat out by the translator (that is, the
# one which has the input/output signals of `i2c` but only contains the `always`
# blocks of `i2c_reg_top`), and converts it into a version with the same
# interface as the real `i2c_reg_top` (minus `devmode_i`).

import re
import sys

from .common import ip, name, regs, windows

with open(sys.argv[2]) as f:
    input = f.read()

reg_re = "|".join(name(reg) for reg in regs if len(reg.fields) > 1)
field_re = "|".join(name(field) for reg in regs for field in reg.fields)
input = re.sub(
    rf"(reg2hw|hw2reg)_({reg_re})_({field_re})_(d|de|q|qe|re)", r"\1.\2.\3.\4", input
)

flat_reg_re = "|".join(name(reg) for reg in regs if len(reg.fields) <= 1)
input = re.sub(
    rf"(reg2hw|hw2reg)_({flat_reg_re})_({field_re})_(d|de|q|qe|re)", r"\1.\2.\4", input
)

# TODO: this is outdated
for i, window in enumerate(windows):
    input = re.sub(rf"reg_req_win_{name(window)}", f"reg_req_win_o[{i}]", input)
    input = re.sub(rf"reg_rsp_win_{name(window)}", f"reg_rsp_win_i[{i}]", input)

input = re.sub(r"logic.*(reg2hw|hw2reg|reg_req_win|reg_rsp_win).*;\n", "", input)

if len(windows) > 0:
    window_ports = f"""
  output logic[85:0][{len(windows) - 1}:0] reg_req_win_o,
  output logic[33:0][{len(windows) - 1}:0] reg_rsp_win_i,"""
else:
    window_ports = ""

input = re.sub(
    rf"module {ip.name}_circuit\([^)]*\)",
    f"""module {ip.name}_reg_top_wrapper(
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
