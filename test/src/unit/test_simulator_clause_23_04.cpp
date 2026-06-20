#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(NestedModuleSimulation, OuterScopeVariableAccessibleFromNestedModule) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  module inner;\n"
      "    initial x = 8'd42;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
}

TEST(NestedModuleSimulation, LocalNameShadowsOuterInSimulation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd10;\n"
      "  module inner;\n"
      "    logic [7:0] x;\n"
      "    initial x = 8'd99;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 10u);
}

TEST(NestedModuleSimulation, PortlessNestedModuleInitialBlockRuns) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  module inner;\n"
      "    initial x = 8'd77;\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 77u);
}

TEST(NestedModuleSimulation, PortedNestedModuleNotInstantiatedDoesNotRun) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd10;\n"
      "  module inner(input a);\n"
      "    initial x = 8'd99;\n"
      "  endmodule\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 10u);
}

// §23.4: the outer name space is visible to the inner module, so a nested
// module may *read* an outer-scope name as well as write one. The outer x is
// set at time 0; one tick later the nested module reads it and copies it into
// the outer y. Observing y == 5 proves the inner module resolved x to the
// enclosing scope's variable.
TEST(NestedModuleSimulation, OuterScopeVariableReadFromNestedModule) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] y;\n"
      "  initial x = 8'd5;\n"
      "  module inner;\n"
      "    initial #1 y = x;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("y");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 5u);
}

}  // namespace
