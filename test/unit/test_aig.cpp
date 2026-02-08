#include <gtest/gtest.h>

#include "synthesis/aig.h"

using namespace delta;

TEST(Aig, LiteralHelpers) {
  for (uint32_t id = 0; id < 10; ++id) {
    auto lit = aig_lit(id, false);
    EXPECT_EQ(aig_var(lit), id);
    EXPECT_FALSE(aig_is_compl(lit));

    auto lit_c = aig_lit(id, true);
    EXPECT_EQ(aig_var(lit_c), id);
    EXPECT_TRUE(aig_is_compl(lit_c));
  }
}

TEST(Aig, AddInput) {
  AigGraph graph;
  auto a = graph.add_input();
  auto b = graph.add_input();
  EXPECT_EQ(graph.inputs.size(), 2);
  EXPECT_NE(aig_var(a), aig_var(b));
}

TEST(Aig, AddAnd) {
  AigGraph graph;
  auto a = graph.add_input();
  auto b = graph.add_input();
  auto c = graph.add_and(a, b);
  EXPECT_GT(graph.node_count(), 2);
  EXPECT_FALSE(aig_is_compl(c));
}

TEST(Aig, NotIsComplement) {
  AigGraph graph;
  auto a = graph.add_input();
  auto not_a = graph.add_not(a);
  EXPECT_EQ(aig_var(not_a), aig_var(a));
  EXPECT_NE(aig_is_compl(not_a), aig_is_compl(a));
}

TEST(Aig, OrViaDeMorgan) {
  AigGraph graph;
  auto a = graph.add_input();
  auto b = graph.add_input();
  auto c = graph.add_or(a, b);
  EXPECT_GT(aig_var(c), 0);
}

TEST(Aig, StructuralHashingDeduplication) {
  AigGraph graph;
  auto a = graph.add_input();
  auto b = graph.add_input();
  auto c1 = graph.add_and(a, b);
  auto c2 = graph.add_and(a, b);
  EXPECT_EQ(c1, c2);
}

TEST(Aig, AddOutput) {
  AigGraph graph;
  auto a = graph.add_input();
  graph.add_output(a);
  ASSERT_EQ(graph.outputs.size(), 1);
  EXPECT_EQ(graph.outputs[0], a);
}

TEST(Aig, XorConstruction) {
  AigGraph graph;
  auto a = graph.add_input();
  auto b = graph.add_input();
  auto x = graph.add_xor(a, b);
  EXPECT_GT(aig_var(x), 0);
}

TEST(Aig, MuxConstruction) {
  AigGraph graph;
  auto s = graph.add_input();
  auto a = graph.add_input();
  auto b = graph.add_input();
  auto m = graph.add_mux(s, a, b);
  EXPECT_GT(aig_var(m), 0);
}
