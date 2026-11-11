#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ProceduralContinuousAssignSim, AssignRhsReevaluatesOnVariableChange) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b, q;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    assign q = a + b;\n"
      "    #1;\n"
      "    a = 8'd100;\n"
      "  end\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 120u);
}

TEST(ProceduralContinuousAssignSim, ForceRhsReevaluatesOnVariableChange) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] b, c, a;\n"
      "  initial begin\n"
      "    b = 8'd1;\n"
      "    c = 8'd2;\n"
      "    force a = b + c;\n"
      "    #1;\n"
      "    b = 8'd50;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 52u);
}

TEST(ProceduralContinuousAssignSim,
     ForceReevaluatesOnFunctionCallArgumentChange) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] b, c, a;\n"
      "  function logic [7:0] dbl(input logic [7:0] x);\n"
      "    return x + x;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    b = 8'd1;\n"
      "    c = 8'd2;\n"
      "    force a = b + dbl(c);\n"
      "    #1;\n"
      "    c = 8'd10;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 21u);
}

TEST(ProceduralContinuousAssignSim, ForceReevaluatesForEachRhsVariableChange) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] b, c, a;\n"
      "  initial begin\n"
      "    b = 8'd1;\n"
      "    c = 8'd2;\n"
      "    force a = b + c;\n"
      "    #1; b = 8'd10;\n"
      "    #1; c = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 30u);
}

TEST(ProceduralContinuousAssignSim,
     ForceOfAConcatenationReevaluatesEachElementsSlice) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] x, y;\n"
      "  logic [11:0] a;\n"
      "  logic [3:0] b;\n"
      "  initial begin\n"
      "    a = 12'hAAA;\n"
      "    b = 4'hF;\n"
      "    x = 16'h1000;\n"
      "    y = 16'h0234;\n"
      "    force {a, b} = x + y;\n"
      "    #1;\n"
      "    x = 16'h4444;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0x467u);
  EXPECT_EQ(b->value.ToUint64(), 0x8u);
}

TEST(ProceduralContinuousAssignSim, ForceFollowsAVariableItReadsByPath) {
  const char* src =
      "module sub; logic [7:0] x = 8'h01; endmodule\n"
      "module t;\n"
      "  sub u1();\n"
      "  struct packed { logic [7:0] f; } s;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    s.f = 8'h02;\n"
      "    force a = u1.x;\n"
      "    force b = s.f;\n"
      "    #1 u1.x = 8'h5a;\n"
      "    s.f = 8'h6b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a"), 0x5au);
  EXPECT_EQ(RunAndGet(src, "b"), 0x6bu);
}

TEST(ProceduralContinuousAssignSim, ForceAndAssignTakeTheTargetsWidth) {
  const char* src =
      "module t;\n"
      "  logic [7:0] a = 8'hFF, b = 8'h01;\n"
      "  logic [15:0] w, v;\n"
      "  wire [7:0] bus;\n"
      "  logic [7:0] hi;\n"
      "  initial begin\n"
      "    force w = a + b;\n"
      "    assign v = a + b;\n"
      "    force bus[7:4] = 2'sb11;\n"
      "    #1 hi = bus;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "w"), 0x0100u);
  EXPECT_EQ(RunAndGet(src, "v"), 0x0100u);
  EXPECT_EQ(RunAndGet(src, "hi") >> 4, 0xFu);
}

TEST(ProceduralContinuousAssignSim, AssignAndForcePatchAnAndGateIntoAnOrGate) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic a, b, c, d;\n"
                       "  wire e;\n"
                       "  and and1 (e, a, b, c);\n"
                       "  initial begin\n"
                       "    $monitor(\"%0d d=%b,e=%b\", $stime, d, e);\n"
                       "    assign d = a & b & c;\n"
                       "    a = 1; b = 0; c = 1;\n"
                       "    #10;\n"
                       "    force d = (a | b | c);\n"
                       "    force e = (a | b | c);\n"
                       "    #10;\n"
                       "    release d;\n"
                       "    release e;\n"
                       "    #10 $finish;\n"
                       "  end\n"
                       "endmodule\n",
                       f)
                .find("0 d=0,e=0\n10 d=1,e=1\n20 d=0,e=0\n"),
            0u);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProceduralContinuousAssignSim, AReleasedNetTakesItsDriversValueAtOnce) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic x, y;\n"
                       "  wire n;\n"
                       "  assign n = x;\n"
                       "  initial begin\n"
                       "    x = 0; y = 1;\n"
                       "    #1 force n = y;\n"
                       "    #1 x = 1; y = 0;\n"
                       "    #1 $display(\"%b\", n);\n"
                       "    release n;\n"
                       "    $display(\"%b\", n);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0\n1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ProceduralContinuousAssignSim,
     InterfaceAndProgramProceduresAssignAndForce) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface I; logic v;\n"
                       "  initial begin\n"
                       "    v = 0; #1 force v = 1; #1 v = 0;\n"
                       "    #1 $display(\"I %b\", v);\n"
                       "    release v; v = 0; #1 $display(\"I %b\", v);\n"
                       "  end\n"
                       "endinterface\n"
                       "program p; logic w;\n"
                       "  initial begin\n"
                       "    assign w = 1; #1 w = 0; $display(\"P %b\", w);\n"
                       "    deassign w; w = 0; $display(\"P %b\", w);\n"
                       "    #10;\n"
                       "  end\n"
                       "endprogram\n"
                       "module t; I u(); p q(); endmodule\n",
                       f),
            "P 1\nP 0\nI 1\nI 0\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
