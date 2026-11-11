#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StructuredProcedureSimulation, AllProcedureTypesCoexist) {
  SimFixture f;
  auto* sum = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] a, b, sum;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "  end\n"
      "  always_comb sum = a + b;\n"
      "  final $display(\"done\");\n"
      "endmodule\n",
      f, "sum");
  ASSERT_NE(sum, nullptr);
  EXPECT_EQ(sum->value.ToUint64(), 30u);
}

TEST(StructuredProcedureSimulation, AlwaysRepeatsUntilTermination) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] count;\n"
      "  initial count = 0;\n"
      "  always #2 count = count + 1;\n"
      "  initial #21 $finish;\n"
      "endmodule\n",
      "count");
  EXPECT_EQ(val, 10u);
}

TEST(StructuredProcedureSimulation, NoImpliedOrderInitialAndAlways) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial a = 8'd42;\n"
      "  always #1 b = a;\n"
      "  initial #2 $finish;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 42u);
  EXPECT_EQ(vb->value.ToUint64(), 42u);
}

TEST(StructuredProcedureSimulation, NoLimitOnAlwaysCount) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a, b, c;\n"
      "  initial begin a = 0; b = 0; c = 0; end\n"
      "  always #2 a = a + 1;\n"
      "  always #2 b = b + 2;\n"
      "  always #2 c = c + 3;\n"
      "  initial #11 $finish;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 5u}, {"b", 10u}, {"c", 15u}});
}

TEST(StructuredProcedureSimulation, InitialAndAlwaysEnabledAtBeginning) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a, b;\n"
      "  initial a = 1;\n"
      "  always begin b = 1; #1 $finish; end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 1u}});
}

TEST(StructuredProcedureSimulation, InitialExecutesOnlyOnce) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    #1;\n"
      "    count = count + 1;\n"
      "  end\n"
      "  initial #10 $finish;\n"
      "endmodule\n",
      "count");
  EXPECT_EQ(val, 1u);
}

TEST(StructuredProcedureSimulation, FinalRunsAtEndOfSimulation) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] marker;\n"
      "  initial begin marker = 1; #5 $finish; end\n"
      "  final marker = 99;\n"
      "endmodule\n",
      "marker");
  EXPECT_EQ(val, 99u);
}

TEST(StructuredProcedureSimulation, FinalExecutesOnlyOnce) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [31:0] marker;\n"
      "  initial begin marker = 0; #1 $finish; end\n"
      "  final marker = marker + 1;\n"
      "endmodule\n",
      "marker");
  EXPECT_EQ(val, 1u);
}

std::string RunThroughTheFinalProcedures(const std::string& src) {
  SimFixture f;
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) {
    LowerAndRun(design, f);
    f.scheduler.EndSimulation();
  }
  std::cout.rdbuf(old_buf);
  EXPECT_FALSE(f.diag.HasErrors());
  return captured.str();
}

TEST(StructuredProcedureSimulation, EveryProcedureKindRunsInAnInterface) {
  EXPECT_EQ(RunThroughTheFinalProcedures(
                "interface ifc;\n"
                "  int a, b, c, d;\n"
                "  initial begin a = 1; #1 a = 2; end\n"
                "  always @(a) b = a * 10;\n"
                "  always_comb c = a + 100;\n"
                "  always_latch if (a > 1) d = a + 5;\n"
                "  final $display(\"a=%0d b=%0d c=%0d d=%0d\", a, b, c, d);\n"
                "endinterface\n"
                "module t;\n"
                "  ifc i();\n"
                "endmodule\n"),
            "a=2 b=20 c=102 d=7\n");
}

TEST(StructuredProcedureSimulation, InitialAndFinalProceduresRunInAProgram) {
  EXPECT_EQ(
      RunThroughTheFinalProcedures("program p;\n"
                                   "  int a;\n"
                                   "  initial begin a = 1; #1 a = 2; end\n"
                                   "  final $display(\"a=%0d\", a);\n"
                                   "endprogram\n"
                                   "module t;\n"
                                   "  p prog();\n"
                                   "endmodule\n"),
      "a=2\n");
}

TEST(StructuredProcedureSimulation, EveryProcedureKindRunsInGenerateBlocks) {
  EXPECT_EQ(RunThroughTheFinalProcedures(
                "module t;\n"
                "  int a, c, d;\n"
                "  int b[2];\n"
                "  case (1)\n"
                "    1: begin : sel initial begin a = 1; #1 a = 2; end end\n"
                "  endcase\n"
                "  for (genvar g = 0; g < 2; g++) begin : gen\n"
                "    always @(a) b[g] = a + g;\n"
                "  end\n"
                "  if (1) begin : cond\n"
                "    always_comb c = a * 3;\n"
                "    always_latch if (a > 1) d = a + 5;\n"
                "    final $display(\"b0=%0d b1=%0d c=%0d d=%0d\", b[0], "
                "b[1], c, d);\n"
                "  end\n"
                "endmodule\n"),
            "b0=2 b1=3 c=6 d=7\n");
}

}  // namespace
