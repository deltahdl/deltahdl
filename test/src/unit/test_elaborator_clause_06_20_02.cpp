// §6.20.2: Value parameters

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// § constant_expression — binary op in parameter elaborates
TEST(ElabA83, ConstantBinaryExprInParamElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int WIDTH = 4 + 4;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.8.4 Primaries — Elaboration
// =============================================================================
// § constant_primary — integer literal in parameter elaborates
TEST(ElabA84, ConstantPrimaryIntegerLiteral) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § constant_primary — real literal in parameter elaborates
TEST(ElabA84, ConstantPrimaryRealLiteral) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter real R = 3.14;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § constant_primary — parameter reference elaborates
TEST(ElabA84, ConstantPrimaryParameterRef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int A = 5;\n"
      "  parameter int B = A;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
