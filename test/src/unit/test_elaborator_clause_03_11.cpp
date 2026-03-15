// Non-LRM tests

#include "fixture_elaborator.h"

namespace {

TEST(DesignBuildingBlockElaboration, ThreeLevelHierarchyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf; endmodule\n"
      "module mid; leaf u0(); endmodule\n"
      "module top; mid u0(); endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DesignBuildingBlockElaboration, GateLevelMux2to1Elaborates) {
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

TEST(DesignBuildingBlockElaboration, PortCommunicationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module inv(input logic a, output logic y);\n"
      "  assign y = ~a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  inv u0(.a(x), .y(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DesignHierarchy, UnknownTopIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc("module m; endmodule\n", f, "nonexistent");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
