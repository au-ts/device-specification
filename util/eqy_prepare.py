# Takes in the version of `i2c_reg_top` spat out by the translator (that is, the
# one which has the input/output signals of `i2c` but only contains the `always`
# blocks of `i2c_reg_top`), and converts it into a version with the same
# interface as the real `i2c_reg_top` (minus `devmode_i`).

import re
import sys

from .common import ip, name, regs

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

input = re.sub(r"logic.*(reg2hw|hw2reg).*;\n", "", input)

input = re.sub(
    rf"module {ip.name}_circuit\([^)]*\)",
    f"""module {ip.name}_reg_top_wrapper(
  input logic clk_i,
  input logic rst_ni,
  input logic[85:0] reg_req_i,
  output logic[33:0] reg_rsp_o,
  output i2c_reg_pkg::i2c_reg2hw_t reg2hw,
  input i2c_reg_pkg::i2c_hw2reg_t hw2reg
)""",
    input,
)

with open(sys.argv[3], "w") as f:
    f.write(input)
