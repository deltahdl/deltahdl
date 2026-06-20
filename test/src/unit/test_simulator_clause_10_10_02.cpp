

#include "fixture_simulator.h"
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

}  // namespace
