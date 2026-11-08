#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(DefparamSimulation, OverriddenParameterVisibleAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int VAL = 1) ();\n"
      "  int observed;\n"
      "  initial observed = VAL;\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "  defparam u.VAL = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("u.observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(DefparamSimulation, LastDefparamVisibleAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int VAL = 1) ();\n"
      "  int observed;\n"
      "  initial observed = VAL;\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "  defparam u.VAL = 10;\n"
      "  defparam u.VAL = 20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("u.observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(DefparamSimulation, OverriddenStringParameterVisibleAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  parameter string P = \"abc\";\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "  defparam u.P = \"xyz\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("u.P");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(Logic4VecToString(var->value), "xyz");
}

TEST(DefparamSimulation, OverriddenStringParameterLongerThanEightCharacters) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  parameter string P = \"abc\";\n"
      "endmodule\n"
      "module top;\n"
      "  child u();\n"
      "  defparam u.P = \"John Smith\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("u.P");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(Logic4VecToString(var->value), "John Smith");
}

TEST(DefparamSimulation, ADefparamNamingAnotherParameterKeepsEveryCharacter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  parameter string P = \"abc\";\n"
      "endmodule\n"
      "module top;\n"
      "  parameter string WANTED = \"John Smith\";\n"
      "  child u();\n"
      "  defparam u.P = WANTED;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("u.P");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(Logic4VecToString(var->value), "John Smith");
}

TEST(DefparamSimulation, RealRightHandSideTakesTheParametersTypeOrItsOwn) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m1;\n"
                       "  real r1, r2;\n"
                       "  parameter [2:0] A = 3'h2;\n"
                       "  parameter B = 3'h2;\n"
                       "  initial begin\n"
                       "    r1 = A; r2 = B;\n"
                       "    $display(\"r1 is %f r2 is %f\", r1, r2);\n"
                       "  end\n"
                       "endmodule\n"
                       "module m2;\n"
                       "  defparam f1.A = 3.1415;\n"
                       "  defparam f1.B = 3.1415;\n"
                       "  m1 f1();\n"
                       "endmodule\n",
                       f),
            "r1 is 3.000000 r2 is 3.141500\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(DefparamSimulation, AnInstanceSelectReachesThatElementAlone) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child;\n"
                       "  parameter P = 1;\n"
                       "endmodule\n"
                       "module cel;\n"
                       "  child c();\n"
                       "endmodule\n"
                       "module top;\n"
                       "  cel u[0:1]();\n"
                       "  cel w[0:1]();\n"
                       "  defparam u[1].c.P = 5;\n"
                       "  defparam w[0].c.P = 7;\n"
                       "  initial #1 $display(\"%0d %0d %0d %0d\", u[0].c.P, "
                       "u[1].c.P, w[0].c.P, w[1].c.P);\n"
                       "endmodule\n",
                       f),
            "1 5 7 1\n");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DefparamSimulation, ANamedBlocksParameterTakesTheDefparamInItsInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child;\n"
                       "  initial begin : blk\n"
                       "    parameter Q = 3;\n"
                       "    #1 $display(\"%m %0d\", Q);\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  defparam u.blk.Q = 6;\n"
                       "  child u();\n"
                       "  child v();\n"
                       "endmodule\n",
                       f),
            "top.u.blk 6\ntop.v.blk 3\n");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DefparamSimulation, SubroutineAndNestedBlockParametersTakeDefparams) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child;\n"
                       "  task t;\n"
                       "    begin : blk\n"
                       "      parameter Q = 3;\n"
                       "      $display(\"t %0d\", Q);\n"
                       "    end\n"
                       "  endtask\n"
                       "  function int f;\n"
                       "    begin : fb\n"
                       "      parameter R = 4;\n"
                       "      return R;\n"
                       "    end\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    begin : a\n"
                       "      begin : b\n"
                       "        parameter S = 5;\n"
                       "        $display(\"ab %0d\", S);\n"
                       "      end\n"
                       "    end\n"
                       "    t;\n"
                       "    $display(\"f %0d\", f());\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  defparam u.t.blk.Q = 6;\n"
                       "  defparam u.f.fb.R = 7;\n"
                       "  defparam top.u.a.b.S = 8;\n"
                       "  child u();\n"
                       "endmodule\n",
                       f),
            "ab 8\nt 6\nf 7\n");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DefparamSimulation, BlockParameterDefparamsFoldReplaceAndReachTasks) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child;\n"
                       "  task t;\n"
                       "    parameter R = 1;\n"
                       "    $display(\"t %0d\", R);\n"
                       "  endtask\n"
                       "  initial begin : blk\n"
                       "    parameter Q = 3;\n"
                       "    $display(\"blk %0d\", Q);\n"
                       "    t;\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  parameter W = 4;\n"
                       "  defparam u.blk.Q = 6;\n"
                       "  defparam u.blk.Q = W + 1;\n"
                       "  defparam u.t.R = 2;\n"
                       "  child u();\n"
                       "endmodule\n",
                       f),
            "blk 5\nt 2\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(DefparamSimulation, AnElementsGenerateLoopFollowsItsOwnDefparam) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf;\n"
                       "  parameter P = 1;\n"
                       "endmodule\n"
                       "module cel;\n"
                       "  parameter N = 1;\n"
                       "  leaf k[0:1]();\n"
                       "  for (genvar i = 0; i < N; i++) begin : g\n"
                       "    leaf c();\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  cel u[0:1]();\n"
                       "  defparam u[1].N = 2;\n"
                       "  initial #1 $display(\"%0d %0d %0d %0d\", u[0].N, "
                       "u[1].N, u[1].g[1].c.P, u[1].k[1].P);\n"
                       "endmodule\n",
                       f),
            "1 2 1 1\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(DefparamSimulation, RealStringAndForkBlockParametersTakeDefparams) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child;\n"
                       "  initial begin : blk\n"
                       "    int v;\n"
                       "    parameter A = 1;\n"
                       "    parameter real R = 1.5;\n"
                       "    parameter string S = \"ab\";\n"
                       "    L: v = 0;\n"
                       "    fork : fk\n"
                       "      parameter F = 2;\n"
                       "      $display(\"%0d %0d %0.2f %s\", A, F, R, S);\n"
                       "    join\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  defparam u.blk.R = 2.25;\n"
                       "  defparam u.blk.S = \"hello\";\n"
                       "  defparam u.blk.fk.F = 9;\n"
                       "  child u();\n"
                       "endmodule\n",
                       f),
            "1 9 2.25 hello\n");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(DefparamSimulation, ADefparamPicksTheGenerateBlockItNames) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child;\n"
                       "  parameter P = 1;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  if (1) begin : g1\n"
                       "    child u();\n"
                       "  end\n"
                       "  if (1) begin : g2\n"
                       "    child u();\n"
                       "  end\n"
                       "  defparam g2.u.P = 5;\n"
                       "  initial #1 $display(\"%0d %0d\", g1.u.P, g2.u.P);\n"
                       "endmodule\n",
                       f),
            "1 5\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(DefparamSimulation, AnIsolatedElementKeepsItsGenerateBlocksDefparam) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf;\n"
                       "  parameter P = 1;\n"
                       "endmodule\n"
                       "module cel;\n"
                       "  if (1) begin : g\n"
                       "    leaf k();\n"
                       "    defparam k.P = 4;\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  cel u[0:1]();\n"
                       "  initial #1 $display(\"%0d %0d\", u[0].g.k.P, "
                       "u[1].g.k.P);\n"
                       "endmodule\n",
                       f),
            "4 4\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(DefparamSimulation, ADefparamResizesADeclarationItsParameterSizes) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module mm #(DWIDTH = 8)();\n"
          "  logic [DWIDTH-1:0] data;\n"
          "  wire [DWIDTH-1:0] w;\n"
          "  initial begin data = '1; #1 $display(\"%h\", data); end\n"
          "endmodule\n"
          "module top;\n"
          "  mm d();\n"
          "  defparam d.DWIDTH = 12;\n"
          "  initial #2 $display(\"%0d %0d %0d\", d.DWIDTH, $bits(d.data),\n"
          "                       $bits(d.w));\n"
          "endmodule\n",
          f),
      "fff\n12 12 12\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(DefparamSimulation, ADefparamResizesAnInterfacesDeclaration) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "interface ifc #(DWIDTH = 8);\n"
          "  logic [DWIDTH-1:0] data;\n"
          "endinterface\n"
          "module top;\n"
          "  ifc d();\n"
          "  defparam d.DWIDTH = 12;\n"
          "  initial begin d.data = '1; #1 $display(\"%h\", d.data); end\n"
          "endmodule\n",
          f),
      "fff\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(DefparamSimulation, ADefparamResizesGenerateBlockDeclarations) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module mm #(W = 4)();\n"
                 "  for (genvar i = 1; i < 3; i++) begin : g\n"
                 "    logic [W*i-1:0] v;\n"
                 "  end\n"
                 "  if (1) begin : b\n"
                 "    wire [W-1:0] n;\n"
                 "  end\n"
                 "  wire s;\n"
                 "endmodule\n"
                 "module top;\n"
                 "  mm d();\n"
                 "  defparam d.W = 5;\n"
                 "  initial #1 $display(\"%0d %0d %0d %0d\", $bits(d.g[1].v),\n"
                 "                      $bits(d.g[2].v), $bits(d.s),\n"
                 "                      $bits(d.b.n));\n"
                 "endmodule\n",
                 f),
      "5 10 1 5\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(DefparamSimulation, ADefparamResizesAnUnpackedDimension) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "module mm #(N = 2)();\n"
                "  logic [3:0] x[N];\n"
                "  logic [3:0] y[N:1];\n"
                "  logic z[2][N];\n"
                "  initial begin\n"
                "    foreach (x[i]) x[i] = i;\n"
                "    #1 $display(\"%0d %0d %0d %0d %0d %0d\", $size(x), x[3],\n"
                "                $size(y), $left(y), $right(y), $size(z, 2));\n"
                "  end\n"
                "endmodule\n"
                "module top;\n"
                "  mm d();\n"
                "  defparam d.N = 4;\n"
                "endmodule\n",
                f),
            "4 3 4 4 1 4\n");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
