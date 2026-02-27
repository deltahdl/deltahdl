// §11.5.1: Vector bit-select and part-select addressing

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// § part_select_range — indexed part select elaborates
TEST(ElabA83, IndexedPartSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial x = data[0+:8];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § constant_range — packed dimension range elaborates
TEST(ElabA83, ConstantRangePackedDimElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial x = data[7:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § primary_literal — part select range elaborates
TEST(ElabA84, PrimaryPartSelectRangeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial x = data[15:8];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elaboration, RealIndex_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  real a = 0.5;\n"
      "  wire [3:0] b;\n"
      "  wire c;\n"
      "  assign c = b[a];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
