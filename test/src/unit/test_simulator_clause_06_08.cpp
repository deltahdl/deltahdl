#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(VariableDeclaration, VariableCreation) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
}

TEST(VariableDeclaration, MultipleVariableCreation) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_NE(f.ctx.FindVariable("a"), nullptr);
  EXPECT_NE(f.ctx.FindVariable("b"), nullptr);
  EXPECT_NE(f.ctx.FindVariable("c"), nullptr);
}

TEST(VariableDeclaration, Logic4StateDefaultInit) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("data");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

TEST(VariableDeclaration, Int2StateDefaultIsZero) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.words[0].aval, 0u);
}

TEST(VariableDeclaration, Bit2StateDefaultIsZero) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
}

TEST(VariableDeclaration, RealDefaultIsZero) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.words[0].aval, 0u);
}

TEST(VariableDeclaration, ShortrealDefaultIsZero) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  shortreal sr;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("sr");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval, 0u);
}

TEST(VariableDeclaration, StaticInitializerAppliesBeforeInitialBlock) {
  auto val = RunAndGet(
      "module t;\n"
      "  int x = 42;\n"
      "  int observed;\n"
      "  initial observed = x;\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 42u);
}

TEST(VariableDeclaration, ChandleDefaultIsNull) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle h;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("h");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval, 0u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
}

TEST(VariableDeclaration, StringDefaultIsRegisteredAsString) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  string s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(f.ctx.IsStringVariable("s"));
}

TEST(VariableDeclaration, EventDefaultIsNewEvent) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event e;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* var = f.ctx.FindVariable("e");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->is_event);
  EXPECT_FALSE(var->is_null_event);
}

TEST(VariableDeclaration, StaticInitializerWithBinaryExpression) {
  auto val = RunAndGet(
      "module t;\n"
      "  int x = 10 * 4 + 2;\n"
      "  int observed;\n"
      "  initial observed = x;\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 42u);
}

TEST(VariableDeclaration, StaticInitializerReferencesEarlierStatic) {
  auto val = RunAndGet(
      "module t;\n"
      "  int base = 7;\n"
      "  int derived = base * 6;\n"
      "  int observed;\n"
      "  initial observed = derived;\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 42u);
}

TEST(VariableDeclaration, StaticInitializerWithClassNew) {
  auto val = RunAndGet(
      "class C;\n"
      "  int v;\n"
      "  function new(int initial_v);\n"
      "    v = initial_v;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C handle = new(42);\n"
      "  int observed;\n"
      "  initial observed = handle.v;\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 42u);
}

TEST(VariableDeclaration, VariableStoresValueBetweenAssignmentAndRead) {
  auto val = RunAndGet(
      "module t;\n"
      "  int x;\n"
      "  int observed;\n"
      "  initial begin\n"
      "    x = 99;\n"
      "    observed = x;\n"
      "  end\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 99u);
}

}  // namespace
