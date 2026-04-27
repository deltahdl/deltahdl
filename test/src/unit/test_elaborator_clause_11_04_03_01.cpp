#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(SignedUnsignedArithmetic, IntVariableElaboratesAsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  initial a = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_signed);
}

TEST(SignedUnsignedArithmetic, ByteVariableElaboratesAsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  initial a = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_signed);
}

TEST(SignedUnsignedArithmetic, ShortintVariableElaboratesAsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  shortint a;\n"
      "  initial a = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_signed);
}

TEST(SignedUnsignedArithmetic, IntegerVariableElaboratesAsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer a;\n"
      "  initial a = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_signed);
}

TEST(SignedUnsignedArithmetic, LongintVariableElaboratesAsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  longint a;\n"
      "  initial a = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_signed);
}

TEST(SignedUnsignedArithmetic, LogicVariableElaboratesAsUnsigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial a = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_FALSE(mod->variables[0].is_signed);
}

TEST(SignedUnsignedArithmetic, SignedFlagPropagatedToSimVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int s;\n"
      "  logic [31:0] u;\n"
      "  initial begin s = 0; u = 0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* vs = f.ctx.FindVariable("s");
  auto* vu = f.ctx.FindVariable("u");
  ASSERT_NE(vs, nullptr);
  ASSERT_NE(vu, nullptr);
  EXPECT_TRUE(vs->is_signed);
  EXPECT_FALSE(vu->is_signed);
}

TEST(SignedUnsignedArithmetic, RealVariableElaboratedAsReal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  initial r = 0.0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_real);
}

TEST(SignedUnsignedArithmetic, ExplicitSignedOnUnsignedTypeElaboratesAsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [7:0] a;\n"
      "  initial a = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_signed);
}

TEST(SignedUnsignedArithmetic, ExplicitUnsignedOnSignedTypeElaboratesAsUnsigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned a;\n"
      "  initial a = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_FALSE(mod->variables[0].is_signed);
}

TEST(SignedUnsignedArithmetic, ExplicitSignedNetElaboratesAsSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire signed [7:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->nets.size(), 1u);
  EXPECT_TRUE(mod->nets[0].is_signed);
}

TEST(SignedUnsignedArithmetic, DefaultNetElaboratesAsUnsigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [7:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->nets.size(), 1u);
  EXPECT_FALSE(mod->nets[0].is_signed);
}

}  // namespace
