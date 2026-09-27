

#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TopLevelModules, TopLevelModuleSimulates) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd42;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
}

TEST(TopLevelModules, DollarRootAssignSimulates) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] a;\n"
      "  initial $root.top.a = 8'd99;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 99u);
}

TEST(TopLevelModules, DollarRootReadSimulates) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] src, dst;\n"
      "  initial begin\n"
      "    src = 8'd77;\n"
      "    dst = $root.top.src;\n"
      "  end\n"
      "endmodule\n",
      f, "dst");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 77u);
}

TEST(TopLevelModules, DollarRootDisambiguatesFromLocalScope) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module child;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd10;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  child child_inst();\n"
      "  initial begin\n"
      "    x = 8'd20;\n"
      "    x = $root.top.x;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 20u);
}

// §23.3.1 (printed page 740): "$root allows explicit access to the top of the
// instantiation tree. This is useful to disambiguate a local path (which
// takes precedence) from the rooted path." Inside A, `B.v` is A's own B and
// `$root.A_top.B.v` the B beside A; the rooted name was stripped to `B.v`
// and read from A like the local one.
TEST(TopLevelModulesAndRoot, RootedPathReachesTheTopLevelInstanceNotTheLocal) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module B;\n"
                 "  int v;\n"
                 "endmodule\n"
                 "module A;\n"
                 "  B B();\n"
                 "  initial #1 $display(\"local %0d rooted %0d full %0d\",\n"
                 "      B.v, $root.A_top.B.v, $root.A_top.A.B.v);\n"
                 "endmodule\n"
                 "module A_top;\n"
                 "  A A();\n"
                 "  B B();\n"
                 "  initial begin A.B.v = 2; B.v = 3; end\n"
                 "endmodule\n",
                 f),
      "local 2 rooted 3 full 2\n");
}

// The same from the other side: a write through the rooted name lands in the
// top-level B and a bare one in A's own, and a net read through each name is
// the net of the instance it names.
TEST(TopLevelModulesAndRoot, RootedPathWritesAndNetsReachTheTopLevelInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module B #(parameter int P = 0);\n"
                       "  int v;\n"
                       "  wire [7:0] w = P;\n"
                       "endmodule\n"
                       "module A;\n"
                       "  B #(.P(5)) B();\n"
                       "  initial begin\n"
                       "    #1 $root.A_top.B.v = 7;\n"
                       "    B.v = 4;\n"
                       "    #1 $display(\"%0d %0d\", B.w, $root.A_top.B.w);\n"
                       "  end\n"
                       "endmodule\n"
                       "module A_top;\n"
                       "  A A();\n"
                       "  B #(.P(9)) B();\n"
                       "  initial #3 $display(\"%0d %0d\", B.v, A.B.v);\n"
                       "endmodule\n",
                       f),
            "5 9\n7 4\n");
}

// §23.3.1 (printed page 740): "A top-level module is implicitly instantiated
// once, and its instance name is the same as the module name", each such
// instance a scope of its own (§23.9), so `int x` in t1 and in t2 are two
// variables. The two tops' declarations were stored under one name, and each
// read the value the other wrote: both xs read 2.
TEST(TopLevelModulesAndRoot, ParallelTopsKeepTheirOwnDeclarations) {
  SimFixture f;
  auto* design = ElaborateSrcAllTops(
      "module t1;\n"
      "  int x = 1, r1, r2;\n"
      "  initial #1 begin r1 = x; r2 = t2.x; end\n"
      "endmodule\n"
      "module t2;\n"
      "  int x = 2, r1, r2, r3;\n"
      "  initial #1 begin r1 = x; r2 = t1.x; r3 = $root.t2.x; end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"x", 1u},
                    {"r1", 1u},
                    {"r2", 2u},
                    {"t2.x", 2u},
                    {"t2.r1", 2u},
                    {"t2.r2", 1u},
                    {"t2.r3", 2u}});
}

}  // namespace
