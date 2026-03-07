#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(Lowerer, VariableCreation) {
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

// §6.8: Variable with initializer gets the initialized value.
TEST(Lowerer, VariableWithInitializer) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §6.8: Multiple variables created from one statement.
TEST(Lowerer, MultipleVariableCreation) {
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

// §6.8: Variable with logic type starts at default (x for 4-state).
TEST(Lowerer, Logic4StateDefaultInit) {
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
  // 4-state default is x (aval=1, bval=1 for each word).
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0xFFu);
}

}  // namespace
