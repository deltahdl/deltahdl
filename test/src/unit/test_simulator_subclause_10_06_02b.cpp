#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ForceReleaseSim, ForcePreventsANonblockingBitSelectAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x[3] <= 1'b1;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

TEST(ForceReleaseSim, ForcePreventsANonblockingPartSelectAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x[3:0] <= 4'hF;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

TEST(ForceReleaseSim, ForcePreventsACompoundAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x += 8'd10;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

TEST(ForceReleaseSim, ForcePreventsAnIncrement) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x++;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

TEST(ForceReleaseSim, ForcePreventsAnIncrementWithoutChangingWhatItYields) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    y = (++x);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);
  EXPECT_EQ(x->value.ToUint64(), 50u);

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 51u);
}

TEST(ForceReleaseSim, ForcePreventsACompoundAssignWrittenAsAnExpression) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    y = (x += 8'd10);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);
  EXPECT_EQ(x->value.ToUint64(), 50u);

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 60u);
}

TEST(ForceReleaseSim, ForcePreventsABitSelectAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x[3] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

TEST(ForceReleaseSim, ForcePreventsAPartSelectAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x[3:0] = 4'hF;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

TEST(ForceReleaseSim, ForcePreventsABitSelectCompoundAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x[3] += 1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

TEST(ForceReleaseSim, ForcePreventsAConcatenationElementAssign) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    force a = 8'd50;\n"
      "    {a, b} = 16'h1234;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_TRUE(a->is_forced);
  EXPECT_EQ(a->value.ToUint64(), 50u);

  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0x34u);
}

TEST(ForceReleaseSim, ForcePreventsATaskBodyAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task poke();\n"
      "    x = 8'd100;\n"
      "  endtask\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    poke();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

TEST(ForceReleaseSim, ForcePreventsAFunctionBodyAssign) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void poke();\n"
      "    x = 8'd100;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    poke();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

TEST(ForceReleaseSim, ForcePreventsACompoundAssignInAFunctionBody) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void poke();\n"
      "    x += 8'd10;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    poke();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

TEST(ForceReleaseSim, ForcePreventsABitSelectAssignInAFunctionBody) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void poke();\n"
      "    x[3] = 1'b1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    poke();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 50u);
}

TEST(ForceReleaseSim, ForcePreventsAConcatenationElementAssignInAFunctionBody) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  function void poke();\n"
      "    {a, b} = 16'h1234;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    force a = 8'd50;\n"
      "    poke();\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_TRUE(a->is_forced);
  EXPECT_EQ(a->value.ToUint64(), 50u);

  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0x34u);
}

TEST(ForceReleaseSim, ReleaseThenATaskBodyAssignResumes) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  task poke();\n"
      "    x = 8'd77;\n"
      "  endtask\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    poke();\n"
      "    release x;\n"
      "    poke();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_FALSE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 77u);
}

TEST(ForceReleaseSim, ReleaseThenACompoundAssignResumes) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x += 8'd10;\n"
      "    release x;\n"
      "    x += 8'd27;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_FALSE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 77u);
}

TEST(ForceReleaseSim, ReleaseThenABitSelectAssignResumes) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    force x = 8'd50;\n"
      "    x[3] = 1'b1;\n"
      "    release x;\n"
      "    x[0] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_FALSE(x->is_forced);

  EXPECT_EQ(x->value.ToUint64(), 51u);
}

TEST(ForceReleaseSim, ForcePreventsAStreamingConcatTargetWrite) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    b = 8'h0F;\n"
      "    force a = 8'd50;\n"
      "    {>> {a, b}} = 16'hABCD;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_TRUE(a->is_forced);
  EXPECT_EQ(a->value.ToUint64(), 50u);

  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0xCDu);
}

TEST(ForceReleaseSim, ForcePreventsANonblockingStreamingConcatTargetWrite) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    b = 8'hF0;\n"
      "    {>> {a, b}} <= 16'h5A3C;\n"
      "    force a = 8'd50;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_TRUE(a->is_forced);
  EXPECT_EQ(a->value.ToUint64(), 50u);

  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(vb->value.ToUint64(), 0x3Cu);
}

TEST(ForceReleaseSim, ReleaseThenAStreamingConcatTargetWriteResumes) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    b = 8'h11;\n"
      "    force a = 8'd50;\n"
      "    release a;\n"
      "    {>> {a, b}} = 16'hABCD;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_FALSE(a->is_forced);
  EXPECT_EQ(a->value.ToUint64(), 0xABu);

  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(vb->value.ToUint64(), 0xCDu);
}

TEST(ForceReleaseSim, ForceOfAQueueElementOverridesAWriteToIt) {
  SimFixture f;
  auto* r1 = RunAndFindVar(
      "module t;\n"
      "  int q[$];\n"
      "  int r1, r2, r3;\n"
      "  initial begin\n"
      "    q.push_back(5);\n"
      "    force q[0] = 9;\n"
      "    r1 = q[0];\n"
      "    q[0] = 3;\n"
      "    r2 = q[0];\n"
      "    release q[0];\n"
      "    q[0] = 7;\n"
      "    r3 = q[0];\n"
      "  end\n"
      "endmodule\n",
      f, "r1");
  ASSERT_NE(r1, nullptr);
  EXPECT_EQ(r1->value.ToUint64(), 9u);
  auto* r2 = f.ctx.FindVariable("r2");
  auto* r3 = f.ctx.FindVariable("r3");
  ASSERT_NE(r2, nullptr);
  ASSERT_NE(r3, nullptr);
  EXPECT_EQ(r2->value.ToUint64(), 9u);
  EXPECT_EQ(r3->value.ToUint64(), 7u);
}

TEST(ForceReleaseSim, ForceOfAnAssociativeElementOverridesAWriteToIt) {
  SimFixture f;
  auto* r1 = RunAndFindVar(
      "module t;\n"
      "  int aa[string];\n"
      "  int r1, r2, r3;\n"
      "  initial begin\n"
      "    aa[\"k\"] = 7;\n"
      "    force aa[\"k\"] = 9;\n"
      "    r1 = aa[\"k\"];\n"
      "    aa[\"k\"] = 3;\n"
      "    r2 = aa[\"k\"];\n"
      "    release aa[\"k\"];\n"
      "    aa[\"k\"] = 4;\n"
      "    r3 = aa[\"k\"];\n"
      "  end\n"
      "endmodule\n",
      f, "r1");
  ASSERT_NE(r1, nullptr);
  EXPECT_EQ(r1->value.ToUint64(), 9u);
  auto* r2 = f.ctx.FindVariable("r2");
  auto* r3 = f.ctx.FindVariable("r3");
  ASSERT_NE(r2, nullptr);
  ASSERT_NE(r3, nullptr);
  EXPECT_EQ(r2->value.ToUint64(), 9u);
  EXPECT_EQ(r3->value.ToUint64(), 4u);
}

TEST(ForceReleaseSim, ForceOfAQueueElementFollowsItsExpression) {
  SimFixture f;
  auto* r1 = RunAndFindVar(
      "module t;\n"
      "  int q[$];\n"
      "  logic [7:0] a, b;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    b = 8'd2;\n"
      "    q.push_back(0);\n"
      "    force q[0] = a + b;\n"
      "    r1 = q[0];\n"
      "    a = 8'd10;\n"
      "    r2 = q[0];\n"
      "  end\n"
      "endmodule\n",
      f, "r1");
  ASSERT_NE(r1, nullptr);
  EXPECT_EQ(r1->value.ToUint64(), 3u);
  auto* r2 = f.ctx.FindVariable("r2");
  ASSERT_NE(r2, nullptr);
  EXPECT_EQ(r2->value.ToUint64(), 12u);
}

}  // namespace
