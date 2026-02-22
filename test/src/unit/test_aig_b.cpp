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

}  // namespace
