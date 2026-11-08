#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_string_var.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(ConcatDisambiguationSim, FixedArrayTargetYieldsElementValues) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  int X;\n"
      "  int A[0:1];\n"
      "  initial begin\n"
      "    X = {16'd1, 16'd2};\n"
      "    A = {16'd1, 16'd2};\n"
      "  end\n"
      "endmodule\n",
      f, "X");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0x00010002u);

  auto* a0 = f.ctx.FindVariable("A[0]");
  auto* a1 = f.ctx.FindVariable("A[1]");
  ASSERT_NE(a0, nullptr);
  ASSERT_NE(a1, nullptr);
  EXPECT_EQ(a0->value.ToUint64(), 1u);
  EXPECT_EQ(a1->value.ToUint64(), 2u);
}

TEST(ConcatDisambiguationSim, QueueTargetYieldsElementValues) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  int X;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    X = {16'd3, 16'd4};\n"
      "    q = {16'd3, 16'd4};\n"
      "  end\n"
      "endmodule\n",
      f, "X");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0x00030004u);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 3u);
  EXPECT_EQ(q->elements[1].ToUint64(), 4u);
}

TEST(ConcatDisambiguationSim, ScalarPacksWhileArrayExtendsPerElement) {
  SimFixture f;
  auto* b = RunAndFindVar(
      "module t;\n"
      "  byte B;\n"
      "  byte BA[2];\n"
      "  initial begin\n"
      "    B = {4'h6, 4'hf};\n"
      "    BA = {4'h6, 4'hf};\n"
      "  end\n"
      "endmodule\n",
      f, "B");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0x6fu);

  auto* ba0 = f.ctx.FindVariable("BA[0]");
  auto* ba1 = f.ctx.FindVariable("BA[1]");
  ASSERT_NE(ba0, nullptr);
  ASSERT_NE(ba1, nullptr);
  EXPECT_EQ(ba0->value.ToUint64(), 0x06u);
  EXPECT_EQ(ba1->value.ToUint64(), 0x0fu);
}

TEST(ConcatDisambiguationSim, ScalarStringFusesWhileArrayKeepsElements) {
  SimFixture f;
  auto* s = RunAndFindVar(
      "module t;\n"
      "  string S1 = \"hello\";\n"
      "  string S2 = \" world\";\n"
      "  string S;\n"
      "  string SA[2];\n"
      "  initial begin\n"
      "    S = {S1, S2};\n"
      "    SA = {S1, S2};\n"
      "  end\n"
      "endmodule\n",
      f, "S");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VecToStr(s->value), "hello world");

  auto* sa0 = f.ctx.FindVariable("SA[0]");
  auto* sa1 = f.ctx.FindVariable("SA[1]");
  ASSERT_NE(sa0, nullptr);
  ASSERT_NE(sa1, nullptr);
  EXPECT_EQ(VecToStr(sa0->value), "hello");
  EXPECT_EQ(VecToStr(sa1->value), " world");
}

TEST(ConcatDisambiguationSim, ScalarPacksWhileDynamicArrayInitDistributes) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  int d[] = {16'd5, 16'd6};\n"
      "  initial x = {16'd5, 16'd6};\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0x00050006u);

  auto* d = f.ctx.FindQueue("d");
  ASSERT_NE(d, nullptr);
  ASSERT_EQ(d->elements.size(), 2u);
  EXPECT_EQ(d->elements[0].ToUint64(), 5u);
  EXPECT_EQ(d->elements[1].ToUint64(), 6u);
}

}  // namespace
