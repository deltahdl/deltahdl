// §13.4.1's Node example (printed page 343), taken one step at a time to find
// which step lost the value #3808 read 0 for. The rest of the subclause's
// simulator cases stand in test_simulator_subclause_13_04_01a.cpp; these three
// share one class and are here so that neither file passes the size gate's
// limit.

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// The class the three cases share: `value_t` is `bit [15:10]` (§6.18), the
// constructor's formal, the protected property and get_val's return are all
// declared with it, and get_first_node hands out a node whose next holds
// 6'h3F.
constexpr const char* kNodeExampleClass =
    "  class Node;\n"
    "    typedef bit [15:10] value_t;\n"
    "    protected Node m_next;\n"
    "    protected value_t m_val;\n"
    "    function new(value_t v); m_val = v; endfunction\n"
    "    function set_next(Node n); m_next = n; endfunction\n"
    "    function Node get_next(); return m_next; endfunction\n"
    "    function value_t get_val(); return m_val; endfunction\n"
    "  endclass\n"
    "  function Node get_first_node();\n"
    "    Node n1, n2;\n"
    "    n1 = new(6'h00);\n"
    "    n2 = new(6'h3F);\n"
    "    n1.set_next(n2);\n"
    "    return n1;\n"
    "  endfunction\n";

// The first step: the value stored through the formal `value_t v`, kept in
// the protected property and handed back by `get_val()`, read into an `int`
// so that neither the local's type nor a select is in the way. 63 is the six
// bits 6'h3F holds; a formal, property or return sized to fewer bits reads
// less, and a `new` that stored nothing reads 0.
TEST(FunctionReturnSim, ClassScopedTypedefValueReturnsThroughAMethodIntoAnInt) {
  SimFixture f;
  auto* got = RunAndFindVar(std::string("module t;\n") + kNodeExampleClass +
                                "  int got;\n"
                                "  initial begin\n"
                                "    Node first_node, next_node;\n"
                                "    first_node = get_first_node();\n"
                                "    next_node = first_node.get_next();\n"
                                "    got = next_node.get_val();\n"
                                "  end\n"
                                "endmodule\n",
                            f, "got");
  ASSERT_NE(got, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(got->value.ToUint64(), 63u);
}

// The second step: the same value held in a local declared `Node::value_t`,
// the class-scoped name §8.23 makes reachable from the procedure. The node is
// built with 8'hFF here rather than the example's 6'h3F: §6.18 makes the local
// the six bits the name stands for, so it keeps 63 of the 255 the property
// handed out, and a local created at the 32-bit carrier a name nothing could
// size falls to reads 255.
TEST(FunctionReturnSim, ClassScopedTypedefLocalHoldsTheReturnedSixBits) {
  SimFixture f;
  auto* got = RunAndFindVar(std::string("module t;\n") + kNodeExampleClass +
                                "  int got;\n"
                                "  initial begin\n"
                                "    Node wide;\n"
                                "    Node::value_t next_value;\n"
                                "    wide = new(8'hFF);\n"
                                "    next_value = wide.get_val();\n"
                                "    got = next_value;\n"
                                "  end\n"
                                "endmodule\n",
                            f, "got");
  ASSERT_NE(got, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(got->value.ToUint64(), 63u);
}

// The third step, which is the example itself and where #3808 read 0:
// `my_bits = next_value[13:10]`. §11.5.1 (printed page 296) has the bit an
// index addresses decided by the declaration, and the declaration is
// `Node::value_t`, so the select names the four bits above the two least
// significant of the six -- 4'hF, 15, of 6'h3F. A procedure's declaration
// recorded no range at all, so the local was addressed as [5:0], the four
// indices 13 to 10 lay outside it, the select read x and the 2-state my_bits
// made that 0.
TEST(FunctionReturnSim,
     NodeExampleStepByStepSelectsTheReturnedValueByItsRange) {
  SimFixture f;
  auto* got = RunAndFindVar(std::string("module t;\n") + kNodeExampleClass +
                                "  int got;\n"
                                "  initial begin\n"
                                "    bit [3:0] my_bits;\n"
                                "    Node first_node, next_node;\n"
                                "    Node::value_t next_value;\n"
                                "    first_node = get_first_node();\n"
                                "    next_node = first_node.get_next();\n"
                                "    next_value = next_node.get_val();\n"
                                "    my_bits = next_value[13:10];\n"
                                "    got = my_bits;\n"
                                "  end\n"
                                "endmodule\n",
                            f, "got");
  ASSERT_NE(got, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(got->value.ToUint64(), 15u);
}

}  // namespace
