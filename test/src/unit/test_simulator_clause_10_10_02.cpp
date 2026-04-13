

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

}  // namespace
