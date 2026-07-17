

#include "fixture_simulator.h"
#include "helpers_string_var.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(ConcatDisambiguationSim, FixedArrayTargetYieldsElementValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int X;\n"
      "  int A[0:1];\n"
      "  initial begin\n"
      "    X = {16'd1, 16'd2};\n"
      "    A = {16'd1, 16'd2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* x = f.ctx.FindVariable("X");
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
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int X;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    X = {16'd3, 16'd4};\n"
      "    q = {16'd3, 16'd4};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* x = f.ctx.FindVariable("X");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0x00030004u);

  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 3u);
  EXPECT_EQ(q->elements[1].ToUint64(), 4u);
}

// §10.10.2: one brace expression takes on different meanings purely from the
// target type. Feeding {4'h6, 4'hf} to a scalar byte makes it a vector
// concatenation, so the two nibbles pack into a single byte (8'h6f). Feeding
// the identical expression to an unpacked byte array makes it an array
// concatenation, so each item becomes one element zero-extended to the element
// width, leaving the nibbles in separate bytes (8'h06, 8'h0f). Observing both
// outcomes from the same right-hand side pins the disambiguation itself, not
// just element distribution.
TEST(ConcatDisambiguationSim, ScalarPacksWhileArrayExtendsPerElement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte B;\n"
      "  byte BA[2];\n"
      "  initial begin\n"
      "    B = {4'h6, 4'hf};\n"
      "    BA = {4'h6, 4'hf};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* b = f.ctx.FindVariable("B");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0x6fu);

  auto* ba0 = f.ctx.FindVariable("BA[0]");
  auto* ba1 = f.ctx.FindVariable("BA[1]");
  ASSERT_NE(ba0, nullptr);
  ASSERT_NE(ba1, nullptr);
  EXPECT_EQ(ba0->value.ToUint64(), 0x06u);
  EXPECT_EQ(ba1->value.ToUint64(), 0x0fu);
}

// §10.10.2, first illustrative example: the same brace expression takes on a
// different meaning purely from its target type when the operands are strings.
// Fed to a scalar string, {S1, S2} is a string concatenation (the "otherwise"
// branch, §11.4.12), so the two operands fuse into "hello world". Fed to an
// unpacked string array, the identical expression is an unpacked array
// concatenation (§10.10), so each operand becomes one whole element and the two
// strings stay separate. The string operand type is a distinct input form from
// the integral/vector cases above, and the divergent runtime values pin the
// disambiguation for it — not merely that elaboration accepts both targets.
TEST(ConcatDisambiguationSim, ScalarStringFusesWhileArrayKeepsElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* s = f.ctx.FindVariable("S");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VecToStr(s->value), "hello world");

  auto* sa0 = f.ctx.FindVariable("SA[0]");
  auto* sa1 = f.ctx.FindVariable("SA[1]");
  ASSERT_NE(sa0, nullptr);
  ASSERT_NE(sa1, nullptr);
  EXPECT_EQ(VecToStr(sa0->value), "hello");
  EXPECT_EQ(VecToStr(sa1->value), " world");
}

// §10.10.2 with a dynamic-array target reached through a declaration
// initializer — a distinct target category and a distinct assignment-like
// syntactic position from the procedural assignments above. The dynamic array
// is built from real §10.10 unpacked-array-concatenation source syntax
// (int d[] = {16'd5, 16'd6}) and its contents are read back from the simulated
// result, so this is the end-to-end check for the consumed §10.10 dependency:
// the initializer braces are disambiguated as an unpacked array concatenation
// and each item becomes one element. The identical right-hand side assigned to
// a scalar int is instead a vector concatenation (§11.4.12), packing the two
// 16-bit items into one 32-bit value.
TEST(ConcatDisambiguationSim, ScalarPacksWhileDynamicArrayInitDistributes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  int d[] = {16'd5, 16'd6};\n"
      "  initial x = {16'd5, 16'd6};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0x00050006u);

  auto* d = f.ctx.FindQueue("d");
  ASSERT_NE(d, nullptr);
  ASSERT_EQ(d->elements.size(), 2u);
  EXPECT_EQ(d->elements[0].ToUint64(), 5u);
  EXPECT_EQ(d->elements[1].ToUint64(), 6u);
}

}  // namespace
