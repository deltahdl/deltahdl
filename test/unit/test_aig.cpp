#include <catch2/catch_test_macros.hpp>

#include "synthesis/aig.h"

using namespace delta;

TEST_CASE("AIG literal helpers", "[aig]") {
    auto lit = aig_lit(5, false);
    REQUIRE(aig_var(lit) == 5);
    REQUIRE_FALSE(aig_is_compl(lit));

    auto lit_c = aig_lit(5, true);
    REQUIRE(aig_var(lit_c) == 5);
    REQUIRE(aig_is_compl(lit_c));
}

TEST_CASE("AIG add input", "[aig]") {
    AigGraph graph;
    auto a = graph.add_input();
    auto b = graph.add_input();
    REQUIRE(graph.inputs.size() == 2);
    REQUIRE(aig_var(a) != aig_var(b));
}

TEST_CASE("AIG add AND", "[aig]") {
    AigGraph graph;
    auto a = graph.add_input();
    auto b = graph.add_input();
    auto c = graph.add_and(a, b);
    REQUIRE(graph.node_count() > 2);
    REQUIRE_FALSE(aig_is_compl(c));
}

TEST_CASE("AIG NOT is complement", "[aig]") {
    AigGraph graph;
    auto a = graph.add_input();
    auto not_a = graph.add_not(a);
    REQUIRE(aig_var(not_a) == aig_var(a));
    REQUIRE(aig_is_compl(not_a) != aig_is_compl(a));
}

TEST_CASE("AIG OR via De Morgan", "[aig]") {
    AigGraph graph;
    auto a = graph.add_input();
    auto b = graph.add_input();
    auto c = graph.add_or(a, b);
    // a | b = ~(~a & ~b)
    // Should produce a valid literal
    REQUIRE(aig_var(c) > 0);
}

TEST_CASE("AIG structural hashing deduplication", "[aig]") {
    AigGraph graph;
    auto a = graph.add_input();
    auto b = graph.add_input();
    auto c1 = graph.add_and(a, b);
    auto c2 = graph.add_and(a, b);
    // Same AND should return the same node
    REQUIRE(c1 == c2);
}

TEST_CASE("AIG add output", "[aig]") {
    AigGraph graph;
    auto a = graph.add_input();
    graph.add_output(a);
    REQUIRE(graph.outputs.size() == 1);
    REQUIRE(graph.outputs[0] == a);
}

TEST_CASE("AIG XOR construction", "[aig]") {
    AigGraph graph;
    auto a = graph.add_input();
    auto b = graph.add_input();
    auto x = graph.add_xor(a, b);
    // XOR produces a valid literal
    REQUIRE(aig_var(x) > 0);
}

TEST_CASE("AIG MUX construction", "[aig]") {
    AigGraph graph;
    auto s = graph.add_input();
    auto a = graph.add_input();
    auto b = graph.add_input();
    auto m = graph.add_mux(s, a, b);
    REQUIRE(aig_var(m) > 0);
}
