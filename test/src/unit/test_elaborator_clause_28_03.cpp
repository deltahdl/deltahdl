// §28.3

#include "fixture_elaborator.h"

namespace {

TEST(GateInstantiation, MuxWithAndOrNotElaborates) {
  EXPECT_TRUE(
      ElabOk("module mux2to1 (input wire a, b, sel,\n"
             "                output logic y);\n"
             "  not g1 (sel_n, sel);\n"
             "  and g2 (a_s, a, sel_n);\n"
             "  and g3 (b_s, b, sel);\n"
             "  or  g4 (y, a_s, b_s);\n"
             "endmodule\n"
             "module top;\n"
             "  logic in1, in2, select;\n"
             "  wire out1;\n"
             "  mux2to1 m1 (.a(in1), .b(in2), .sel(select), .y(out1));\n"
             "endmodule\n"));
}

}  // namespace
