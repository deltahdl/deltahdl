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

TEST(GateElaboration, AllElaborableGatesThroughFullPipeline) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  wire a, b, c, y1, y2, y3, y4, y5, y6, o1, o2, n1, n2;\n"
      "  and (y1, a, b);\n"
      "  nand (y2, a, b);\n"
      "  or (y3, a, b);\n"
      "  nor (y4, a, b);\n"
      "  xor (y5, a, b);\n"
      "  xnor (y6, a, b);\n"
      "  buf (o1, a);\n"
      "  not (o2, a);\n"
      "  pullup (n1);\n"
      "  pulldown (n2);\n"
      "endmodule\n"));
}

}  // namespace
