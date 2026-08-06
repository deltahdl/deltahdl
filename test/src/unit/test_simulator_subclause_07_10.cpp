#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

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

// Cross-link with §10.10: §7.10 promises that the empty unpacked array
// concatenation `{}` denotes the empty queue. The same TryQueueBlockingAssign
// path that satisfies §10.10's zero-item rule must drain a previously
// populated queue down to zero elements here.
TEST(QueueAccess, EmptyConcatProducesEmptyQueue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$] = '{5, 6, 7};\n"
      "  initial q = {};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elements.size(), 0u);
}

// Each queue element is named by its ordinal position: index 0 is the first
// element, index `$` is the last. With a three-element queue this becomes
// q[0] == 10 and q[$] == 30, which exercises the simulator's $-as-last-index
// binding in EvalQueueIndex.
TEST(QueueAccess, ZeroIndexIsFirstAndDollarIsLast) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$] = '{10, 20, 30};\n"
      "  int first;\n"
      "  int last;\n"
      "  initial begin\n"
      "    first = q[0];\n"
      "    last = q[$];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* first = f.ctx.FindVariable("first");
  auto* last = f.ctx.FindVariable("last");
  ASSERT_NE(first, nullptr);
  ASSERT_NE(last, nullptr);
  EXPECT_EQ(first->value.ToUint64(), 10u);
  EXPECT_EQ(last->value.ToUint64(), 30u);
}

}  // namespace
