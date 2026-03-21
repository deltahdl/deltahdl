#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §A.8.4: primary_literal — integer literal elaborates
TEST(PrimaryElaboration, IntegerLiteralElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  assign x = 8'd42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §A.8.4: constant_primary — parameter identifier in constant context
TEST(PrimaryElaboration, ConstantPrimaryParameterElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter P = 8;\n"
      "  logic [P-1:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §A.8.4: hierarchical_identifier with select elaborates
TEST(PrimaryElaboration, HierarchicalIdentifierSelectElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  logic x;\n"
      "  assign x = data[3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §A.8.4: assignment_pattern_expression elaborates
TEST(PrimaryElaboration, AssignmentPatternElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [3];\n"
      "  initial arr = '{1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §A.8.4: concatenation with range_expression elaborates
TEST(PrimaryElaboration, ConcatenationWithRangeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  logic [3:0] x;\n"
      "  initial x = {a, b}[3:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §A.8.4: null primary elaborates
TEST(PrimaryElaboration, NullPrimaryElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class C; endclass\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = null;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
