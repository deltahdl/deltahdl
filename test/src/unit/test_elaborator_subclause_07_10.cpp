#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(QueueDeclarationElaboration, UnboundedQueueDimension) {
  ElabFixture f;
  auto* design = Elaborate("module m; int q [$]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_queue);
  EXPECT_EQ(mod->variables[0].queue_max_size, -1);
}

// Records the optional right bound from `queue_dimension ::= [ $ [ :
// constant_expression ] ]`. The stored max_size is the size of the queue
// (last index N plus one).
TEST(QueueDeclarationElaboration, BoundedQueueDimensionRecordsCapacity) {
  ElabFixture f;
  auto* design = Elaborate("module m; bit b [$:7]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_queue);
  EXPECT_EQ(mod->variables[0].queue_max_size, 8);
}

// Observes the "constant_expression shall evaluate to a positive integer
// value" rule. Anything non-positive (zero or negative) trips the same check
// in the elaborator; a single negative-bound case suffices to pin the rule.
TEST(QueueDeclarationElaboration, NonPositiveBoundEmitsError) {
  ElabFixture f;
  auto* design = Elaborate("module m; int q [$:-1]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §7.10's bound is a constant_expression, which per §11.2.1 may name a
// localparam. A localparam bound shall resolve to the queue's capacity exactly
// as a literal bound does; here N == 7 yields size N+1 == 8.
TEST(QueueDeclarationElaboration, LocalparamBoundRecordsCapacity) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam int N = 7;\n"
      "  bit b [$:N];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const RtlirVariable* q = nullptr;
  for (auto& v : mod->variables)
    if (v.name == "b") q = &v;
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(q->is_queue);
  EXPECT_EQ(q->queue_max_size, 8);
}

// The same constant-expression path must still enforce "shall evaluate to a
// positive integer": a parameter that evaluates non-positive trips the error,
// proving the bound is genuinely evaluated in the parameter scope rather than
// silently dropped (which would leave the queue unbounded with no diagnostic).
TEST(QueueDeclarationElaboration, ParameterNonPositiveBoundEmitsError) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int N = 0;\n"
      "  int q [$:N];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
