// Non-LRM tests

#include <gtest/gtest.h>
#include "synthesis/aig.h"

using namespace delta;

namespace {

TEST(Aig, LiteralHelpers) {
  for (uint32_t id = 0; id < 10; ++id) {
    auto lit = AigLit(id, false);
    EXPECT_EQ(AigVar(lit), id);
    EXPECT_FALSE(AigIsCompl(lit));

    auto lit_c = AigLit(id, true);
    EXPECT_EQ(AigVar(lit_c), id);
    EXPECT_TRUE(AigIsCompl(lit_c));
  }
}

TEST(Aig, AddInput) {
  AigGraph graph;
  auto a = graph.AddInput();
  auto b = graph.AddInput();
  EXPECT_EQ(graph.inputs.size(), 2);
  EXPECT_NE(AigVar(a), AigVar(b));
}

TEST(Aig, AddAnd) {
  AigGraph graph;
  auto a = graph.AddInput();
  auto b = graph.AddInput();
  auto c = graph.AddAnd(a, b);
  EXPECT_GT(graph.NodeCount(), 2);
  EXPECT_FALSE(AigIsCompl(c));
}

TEST(Aig, NotIsComplement) {
  AigGraph graph;
  auto a = graph.AddInput();
  auto not_a = graph.AddNot(a);
  EXPECT_EQ(AigVar(not_a), AigVar(a));
  EXPECT_NE(AigIsCompl(not_a), AigIsCompl(a));
}

TEST(Aig, OrViaDeMorgan) {
  AigGraph graph;
  auto a = graph.AddInput();
  auto b = graph.AddInput();
  auto c = graph.AddOr(a, b);
  EXPECT_GT(AigVar(c), 0);
}

}  // namespace
