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
  // observed is declared in child, instantiated as u, so its runtime storage is
  // u.observed; query the hierarchical name (the scheduler leaves no current
  // process installed once it goes idle, so a bare name resolves in top scope).
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
  // observed lives in child instance u; query u.observed (no current process is
  // installed once the scheduler is idle, so a bare name resolves in top
  // scope).
  auto* var = f.ctx.FindVariable("u.observed");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// A defparam over a string parameter declared as a module item, which is the
// one shape where Elaborator::ElaborateParamDecl has already recorded the
// declaration's own characters in RtlirParamDecl::resolved_string by the time
// the defparam replaces resolved_value. Lowerer::LowerParams reads
// resolved_string for a string parameter, so a lowering that read it here
// would run the design with "abc" -- the value the defparam overrode -- and
// report nothing.
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

// Ten characters is past what EvalDefparamOverride's int64_t can carry, so this
// case separates the recording of the override's own characters from the §11.10
// packed fold beside it. The three-character case above passes on the packed
// value alone and says nothing about a longer one.
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

// §23.10.1: a defparam's right-hand side is a constant expression, and §11.2.1
// makes a parameter one. The name is written in the module holding the defparam
// statement, so that module's parameters are what supplies the characters.
// Before this the fold failed, ReplaceStringParamValue cleared is_string_value,
// and the lowering fell back to the packed number.
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

// §23.10 (printed page 764), the clause's own example: the defparam of f1.A
// with 3.1415 converts the floating-point 3.1415 to the fixed-point 3, and the
// defparam of f1.B with 3.1415 replaces B's 3'h2 with the floating-point
// 3.1415. Folded as an integer, each right-hand side was reported as not
// constant and both read 0.0.
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

// §23.10.1 with §23.6: a defparam may select one instance of an array of
// instances, u[1], and changes the parameter in that instance alone. The
// elements shared one elaborated module, so the step was never matched (a
// "target not found" warning), and matched it would have changed u[0] too.
TEST(DefparamSimulation, AnInstanceSelectReachesThatElementAlone) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module child;\n"
                 "  parameter P = 1;\n"
                 "endmodule\n"
                 "module cel;\n"
                 "  child c();\n"
                 "endmodule\n"
                 "module top;\n"
                 "  cel u[0:1]();\n"
                 "  defparam u[1].c.P = 5;\n"
                 "  initial #1 $display(\"%0d %0d\", u[0].c.P, u[1].c.P);\n"
                 "endmodule\n",
                 f),
      "1 5\n");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §23.10.1 with §23.10.2: a parameter a named block declares is redefined by a
// defparam naming it through the block, u.blk.Q, in that instance alone: u
// reads 6 and v keeps its declared 3. The path reached no parameter, the
// block's being a statement of the body rather than one of the module's, and
// was reported as finding no target.
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

// §23.10.2 lets a defparam redefine a parameter declared in a task or a
// function as well as in a named block, and a named block nested in another
// is reached through both, from the instance or from the top (§23.8):
// u.t.blk.Q, u.f.fb.R and top.u.a.b.S each take their defparam's value.
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

// §23.10.1: the value a block parameter's defparam gives is folded where the
// statement stands, so `W + 1` reads top's W; a parameter a task declares
// directly takes one through the task, u.t.R; and of two defparams naming the
// same parameter the later is the one kept.
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

// §23.10.1 with §27.4: the element u[1] a defparam changes is given a module
// of its own with the generate constructs still to be elaborated in it, so
// its loop generates two blocks while u[0]'s generates one, and the array of
// leaf instances the element holds is copied once, its elements sharing the
// copy as they shared the original.
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

}  // namespace
