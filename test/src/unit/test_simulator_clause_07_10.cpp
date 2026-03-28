#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(QueueAccess, OutOfBoundsReturnsX) {
  SimFixture f;
  auto* q = f.ctx.CreateQueue("q", 16);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 100));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 200));

  auto in_result = EvalExpr(MakeSelect(f.arena, "q", 1), f.ctx, f.arena);
  EXPECT_EQ(in_result.ToUint64(), 200u);
  EXPECT_TRUE(in_result.IsKnown());

  auto oob_result = EvalExpr(MakeSelect(f.arena, "q", 5), f.ctx, f.arena);
  EXPECT_FALSE(oob_result.IsKnown());
}

TEST(QueueAccess, DefaultInitializationIsEmpty) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 0u);
}

}  // namespace
