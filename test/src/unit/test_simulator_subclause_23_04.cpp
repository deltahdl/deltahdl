#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(NestedModuleSimulation, OuterScopeVariableAccessibleFromNestedModule) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  module inner;\n"
      "    initial x = 8'd42;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
}

TEST(NestedModuleSimulation, LocalNameShadowsOuterInSimulation) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd10;\n"
      "  module inner;\n"
      "    logic [7:0] x;\n"
      "    initial x = 8'd99;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 10u);
}

TEST(NestedModuleSimulation, PortlessNestedModuleInitialBlockRuns) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  module inner;\n"
      "    initial x = 8'd77;\n"
      "  endmodule\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 77u);
}

TEST(NestedModuleSimulation, PortedNestedModuleNotInstantiatedDoesNotRun) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd10;\n"
      "  module inner(input a);\n"
      "    initial x = 8'd99;\n"
      "  endmodule\n"
      "endmodule\n",
      f, "x");
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
  auto* v = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] y;\n"
      "  initial x = 8'd5;\n"
      "  module inner;\n"
      "    initial #1 y = x;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 5u);
}

// §23.4: "The outer name space is visible to the inner module so that any name
// declared there can be used, unless hidden by a local name, provided the
// module is declared and instantiated in the same scope." That visibility is
// what tells a nested declaration apart from a module declared elsewhere and
// merely instantiated, which §23.9 stops at the module boundary. The cases
// above establish the visibility itself; this one establishes that it belongs
// to the nested declaration rather than to instantiation in general, by
// declaring `outer` at the top level and instantiating it beside a nested
// `inner` that reads the same name. Only the nested one may read `x`, so the
// two answers must differ, and asserting them together is what stops a change
// to either rule from silently taking the other with it.
TEST(NestedModuleSimulation, OuterNameIsVisibleToANestedDeclarationOnly) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module outer;\n"
      "  logic [7:0] seen;\n"
      "  initial #1 seen = x;\n"
      "endmodule\n"
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] nested_seen;\n"
      "  initial x = 8'd42;\n"
      "  module inner;\n"
      "    initial #1 nested_seen = x;\n"
      "  endmodule\n"
      "  inner i1();\n"
      "  outer o1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  // The nested declaration reads the enclosing module's x.
  auto* nested_seen = f.ctx.FindVariable("nested_seen");
  ASSERT_NE(nested_seen, nullptr);
  EXPECT_EQ(nested_seen->value.ToUint64(), 42u);

  // The separately declared module does not: its own scope declares no x, and
  // §23.9 stops the search for a variable at its module boundary.
  auto* seen = f.ctx.FindVariable("o1.seen");
  ASSERT_NE(seen, nullptr);
  EXPECT_NE(seen->value.ToUint64(), 42u);
}

}  // namespace
