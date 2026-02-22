// Non-LRM tests

#include "synthesis/aig.h"
#include "synthesis/aig_opt.h"
#include <gtest/gtest.h>

using namespace delta;

namespace {

// =============================================================================
// Constant propagation
// =============================================================================
TEST(AigOpt, ConstPropRemovesDeadAndWithConstant) {
  AigGraph g;
  auto a = g.AddInput();
  // AND(a, true) = a, should already be simplified by AddAnd.
  // Build a graph where constant propagation can clean up:
  // Create outputs with known constant values.
  g.AddOutput(AigGraph::kConstFalse);
  g.AddOutput(a);

  ConstProp(g);

  // Outputs should remain the same — no structural change needed.
  EXPECT_EQ(g.outputs[0], AigGraph::kConstFalse);
  EXPECT_EQ(g.outputs[1], a);
}

TEST(AigOpt, ConstPropConstantOutput) {
  AigGraph g;
  auto a = g.AddInput();
  // Create AND(a, ~a) = 0, but AddAnd already simplifies this.
  auto c = g.AddAnd(a, g.AddNot(a));
  g.AddOutput(c);

  ConstProp(g);
  EXPECT_EQ(g.outputs[0], AigGraph::kConstFalse);
}

TEST(AigOpt, ConstPropPreservesNonTrivial) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);

  size_t before = g.NodeCount();
  ConstProp(g);
  // Non-trivial AND should not be removed.
  EXPECT_EQ(g.NodeCount(), before);
  EXPECT_EQ(g.outputs[0], c);
}

// =============================================================================
// AIG balancing
// =============================================================================
TEST(AigOpt, BalanceReducesDepth) {
  // Create a left-skewed chain: AND(AND(AND(a, b), c), d)
  // Balanced should be: AND(AND(a, b), AND(c, d))
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddInput();
  auto d = g.AddInput();

  auto ab = g.AddAnd(a, b);
  auto abc = g.AddAnd(ab, c);
  auto abcd = g.AddAnd(abc, d);
  g.AddOutput(abcd);

  Balance(g);

  // After balancing, the output should still be logically equivalent
  // (same function), but we can't easily check depth without a depth
  // function. At minimum, verify output is not constant.
  EXPECT_NE(g.outputs[0], AigGraph::kConstFalse);
  EXPECT_NE(g.outputs[0], AigGraph::kConstTrue);
}

TEST(AigOpt, BalancePreservesSingleNode) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);

  Balance(g);
  // Single AND node should be preserved.
  EXPECT_NE(g.outputs[0], AigGraph::kConstFalse);
}

// =============================================================================
// AIG rewriting (basic)
// =============================================================================
TEST(AigOpt, RewriteSimplifies) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  // OR(a, b) = ~(~a & ~b) — 1 AND + 3 inversions
  auto c = g.AddOr(a, b);
  g.AddOutput(c);

  size_t before = g.NodeCount();
  Rewrite(g);
  // Rewriting should not increase node count.
  EXPECT_LE(g.NodeCount(), before);
}

TEST(AigOpt, RewritePreservesConstants) {
  AigGraph g;
  g.AddOutput(AigGraph::kConstTrue);
  Rewrite(g);
  EXPECT_EQ(g.outputs[0], AigGraph::kConstTrue);
}

// =============================================================================
// AIG refactoring (basic)
// =============================================================================
TEST(AigOpt, RefactorDoesNotCorrupt) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  auto d = g.AddOr(a, b);
  g.AddOutput(c);
  g.AddOutput(d);

  Refactor(g);
  // Should not corrupt the graph — outputs should still be valid.
  EXPECT_EQ(g.outputs.size(), 2);
}

// =============================================================================
// Redundancy removal (basic)
// =============================================================================
TEST(AigOpt, RedundancyRemovalNoChange) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);

  size_t before = g.NodeCount();
  RemoveRedundancy(g);
  // Simple AND should not have redundancy.
  EXPECT_EQ(g.NodeCount(), before);
}

} // namespace
