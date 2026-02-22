// Non-LRM tests

#include <gtest/gtest.h>
#include "synthesis/aig.h"

using namespace delta;

namespace {

TEST(Aig, StructuralHashingDeduplication) {
  AigGraph graph;
  auto a = graph.AddInput();
  auto b = graph.AddInput();
  auto c1 = graph.AddAnd(a, b);
  auto c2 = graph.AddAnd(a, b);
  EXPECT_EQ(c1, c2);
}

TEST(Aig, AddOutput) {
  AigGraph graph;
  auto a = graph.AddInput();
  graph.AddOutput(a);
  ASSERT_EQ(graph.outputs.size(), 1);
  EXPECT_EQ(graph.outputs[0], a);
}

TEST(Aig, XorConstruction) {
  AigGraph graph;
  auto a = graph.AddInput();
  auto b = graph.AddInput();
  auto x = graph.AddXor(a, b);
  EXPECT_GT(AigVar(x), 0);
}

TEST(Aig, MuxConstruction) {
  AigGraph graph;
  auto s = graph.AddInput();
  auto a = graph.AddInput();
  auto b = graph.AddInput();
  auto m = graph.AddMux(s, a, b);
  EXPECT_GT(AigVar(m), 0);
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

}  // namespace
