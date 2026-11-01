#include <gtest/gtest.h>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_generate_block_items.h"
#include "helpers_reported_error.h"

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

// Observes the rule that constant_expression evaluate to a positive integer.
// Anything non-positive (zero or negative) trips the same check in the
// elaborator; a single negative-bound case suffices to pin the rule.
TEST(QueueDeclarationElaboration, NonPositiveBoundEmitsError) {
  ElabFixture f;
  auto* design = Elaborate("module m; int q [$:-1]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "queue bound must be a positive integer", 1,
                            "7.10"));
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

// The same constant-expression path must still enforce the positive-integer
// rule: a parameter that evaluates non-positive trips the error, proving the
// bound is genuinely evaluated in the parameter scope rather than silently
// dropped (which would leave the queue unbounded with no diagnostic).
TEST(QueueDeclarationElaboration, ParameterNonPositiveBoundEmitsError) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int N = 0;\n"
      "  int q [$:N];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "queue bound must be a positive integer", 3,
                            "7.10"));
}

// §27.2 makes a generate block a collection of module items, so a queue a
// procedure inside one declares takes a positive bound, folded in the block
// instance when the block's genvar gives it.
TEST(QueueDeclarationElaboration, BoundInsideGenerateBlocksIsChecked) {
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "logic y;", "initial begin int q[$:-1]; end"},
      "queue bound must be a positive integer", "7.10"));
  EXPECT_TRUE(AcceptedInsideGenerateBlocks(
      {"", "logic y;", "initial begin int q[$:1]; end"}));
  {
    ElabFixture f;
    ElaborateSrc(
        "module m;\n"
        "  for (genvar i = 0; i < 2; i++) begin : g\n"
        "    initial begin int q[$:i]; end\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "queue bound must be a positive integer", 3,
                              "7.10"));
  }
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  for (genvar i = 1; i < 3; i++) begin : g\n"
             "    initial begin int q[$:i]; end\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
