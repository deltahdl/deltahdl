#include "fixture_elaborator.h"

using namespace delta;

namespace {

// "Constants are named data objects that never change."
// Procedural assignment to a parameter shall be rejected.
TEST(ConstantImmutability, BlockingAssignToParameterIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter int P = 5;\n"
      "  initial P = 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ConstantImmutability, NonblockingAssignToParameterIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter int P = 5;\n"
      "  initial P <= 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ConstantImmutability, BlockingAssignToLocalparamIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  localparam int LP = 5;\n"
      "  initial LP = 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ConstantImmutability, BlockingAssignToSpecparamIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  specparam DELAY = 10;\n"
      "  initial DELAY = 20;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// "Parameter constants can be initialized with a literal."
TEST(ParameterConstantInit, ParameterLogicInitWithLiteral) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter logic flag = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "flag");
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 1);
}

TEST(ParameterConstantInit, LocalparamByteInitWithStringLiteral) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam byte colon1 = \":\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "colon1");
  EXPECT_TRUE(p.is_localparam);
}

TEST(ParameterConstantInit, SpecparamInitWithIntegerLiteral) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam delay = 10;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// All four constant kinds coexist in a single module.
TEST(ConstantKinds, AllFourKindsCoexist) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = 1;\n"
      "  localparam int LP = 2;\n"
      "  specparam SP = 3;\n"
      "  const int C = 4;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// "Each parameter may be assigned a default value when declared."
TEST(ParameterConstantInit, DefaultValueAssignedWhenDeclared) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 1u);
  auto& p = design->top_modules[0]->params[0];
  EXPECT_EQ(p.name, "WIDTH");
  EXPECT_NE(p.default_value, nullptr);
  EXPECT_TRUE(p.is_resolved);
  EXPECT_EQ(p.resolved_value, 8);
}

}  // namespace
