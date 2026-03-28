#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "simulator/eval_array.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(QueueSizeSimulation, SizeReturnsCount) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "size", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 3u);
}

TEST(QueueSizeSimulation, SizeReturnsZeroForEmpty) {
  SimFixture f;
  f.ctx.CreateQueue("q", 32);
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "size", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(QueueSizeSimulation, ReturnsThirtyTwoBitInt) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20});
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "size", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.width, 32u);
}

TEST(QueueSizeSimulation, SingleElementReturnsOne) {
  SimFixture f;
  MakeQueue(f, "q", {42});
  Logic4Vec out{};
  auto* call = MakeMethodCall(f.arena, "q", "size", {});
  bool ok = TryEvalQueueMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
}

TEST(QueueSizeSimulation, PropertyAccessReturnsCount) {
  SimFixture f;
  MakeQueue(f, "q", {10, 20, 30});
  Logic4Vec out{};
  bool ok = TryEvalQueueProperty("q", "size", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 3u);
}

TEST(QueueSizeSimulation, PropertyAccessReturnsZeroForEmpty) {
  SimFixture f;
  f.ctx.CreateQueue("q", 32);
  Logic4Vec out{};
  bool ok = TryEvalQueueProperty("q", "size", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(QueueSizeSimulation, QueueSizeNoParens) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q [$];\n"
      "  logic [31:0] s;\n"
      "  initial begin\n"
      "    q.push_back(8'h01);\n"
      "    q.push_back(8'h02);\n"
      "    q.push_back(8'h03);\n"
      "    s = q.size;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 3u);
}

TEST(QueueSizeSimulation, SizeInForLoopCondition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q [$] = '{10, 20, 30};\n"
      "  int total;\n"
      "  initial begin\n"
      "    total = 0;\n"
      "    for (int j = 0; j < q.size; j++)\n"
      "      total = total + q[j];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("total")->value.ToUint64(), 60u);
}

}  // namespace
