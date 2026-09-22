// §13.4.1's Node example (printed page 343), taken one step at a time to find
// which step lost the value #3808 read 0 for. The rest of the subclause's
// simulator cases stand in test_simulator_subclause_13_04_01a.cpp; these three
// share one class and are here so that neither file passes the size gate's
// limit. After them, the implicit return variable's type (printed page 342)
// where it is a string or a class.

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

// §13.4.1 (printed page 342): the variable a function's own name declares has
// the function's return type, and §6.16 (printed 112) makes a string as long
// as the text last assigned to it. A module function's, a class method's and a
// package function's `f = "hello world"` each hand out all eleven characters;
// a variable created at a 32-bit carrier kept the last four, `orld`.
TEST(FunctionReturnSim, StringReturnVariableAssignedByNameHandsOutAllOfIt) {
  SimFixture f;
  std::string out = RunCapture(
      "package p;\n"
      "  function string pf(); pf = \"hello world\"; endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  import p::*;\n"
      "  function string mf(); mf = \"hello world\"; endfunction\n"
      "  class C;\n"
      "    function string cm(); cm = \"hello world\"; endfunction\n"
      "  endclass\n"
      "  C c = new;\n"
      "  initial $display(\"<%s> <%s> <%s>\", mf(), c.cm(), pf());\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "<hello world> <hello world> <hello world>\n");
}

// §13.4.1 with §6.16.1 and §21.3.3: inside the body the implicit variable is
// the string it was declared, so `f.len()` counts the eleven characters
// assigned to it and `$swrite(f, "%m")` writes the whole hierarchical name,
// the ten characters of t.scope_of, into it. At the 32-bit carrier, len()
// read 0 and $swrite kept the name's last four characters.
TEST(FunctionReturnSim, StringReturnVariableIsAStringInsideTheBody) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  function string scope_of();\n"
      "    scope_of = \"hello world\";\n"
      "    $display(\"%0d\", scope_of.len());\n"
      "    $swrite(scope_of, \"%m\");\n"
      "  endfunction\n"
      "  initial $display(\"<%s>\", scope_of());\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "11\n<t.scope_of>\n");
}

// §11.4.14 (printed page 291) reports a stream wider than its target only
// where the target is a fixed-size variable, and resizes a dynamically sized
// one to it, which §6.16 (printed 112) makes a string, so `f = {>>{q}}` on a
// queue of strings fills the implicit string variable whatever it held before
// -- the empty string, or the two characters `xy` assigned ahead of the
// stream. Both read `abcdef`; the 32-bit carrier was reported narrower than
// the 48-bit stream, and a string holding `xy` was reported so by the same
// check.
TEST(FunctionReturnSim, StringReturnVariableTakesAStreamOfStrings) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  function automatic string join_ret(ref string i[$]);\n"
      "    join_ret = {>>{i}};\n"
      "  endfunction\n"
      "  function automatic string join_over(ref string i[$]);\n"
      "    join_over = \"xy\";\n"
      "    join_over = {>>{i}};\n"
      "  endfunction\n"
      "  string q[$];\n"
      "  initial begin\n"
      "    q.push_back(\"ab\");\n"
      "    q.push_back(\"cdef\");\n"
      "    $display(\"<%s> <%s>\", join_ret(q), join_over(q));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  // The report is the run's, raised after has_errors was read.
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "<abcdef> <abcdef>\n");
}

// §13.4.1 (printed page 342) with §8.7 (printed 184): the implicit variable
// has the function's return type, and the left-hand side of an assignment of
// `new` decides the class constructed, so `mk = new` in a function returning M
// constructs an M and the call hands its handle out -- from a module function,
// a static method and an instance method alike, with and without constructor
// arguments. Each handle is non-null and the object's `v` reads through it:
// 4 from the default, 9 from the argument. The variable had no class recorded
// under its name, so the `new` was evaluated as a value and the call returned
// null.
TEST(FunctionReturnSim, ClassReturnVariableAssignedNewConstructsTheObject) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class M;\n"
      "    int v = 4;\n"
      "    function new(int a = 4); v = a; endfunction\n"
      "    static function M by_name(); by_name = new; endfunction\n"
      "    function M inst_by_name(); inst_by_name = new(9); endfunction\n"
      "  endclass\n"
      "  function M mk(); mk = new; endfunction\n"
      "  M m, x, s, i;\n"
      "  initial begin\n"
      "    x = new;\n"
      "    m = mk(); s = M::by_name(); i = x.inst_by_name();\n"
      "    $display(\"%0d %0d %0d\", m == null, s == null, i == null);\n"
      "    $display(\"%0d %0d %0d\", m.v, s.v, i.v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "0 0 0\n4 4 9\n");
}

// §13.4.1: a `return` writes the same implicit variable an assignment to the
// function's name does, so `return new` and `return new(7)` in a function
// returning M construct an M as `mk = new` does, from a module function and
// from a static method of a package's class alike. The handles are non-null
// and `v` reads 4 and 7 through them; evaluated as a value, the `new`
// returned null.
TEST(FunctionReturnSim, ReturnNewConstructsAnObjectOfTheReturnType) {
  SimFixture f;
  std::string out = RunCapture(
      "package p;\n"
      "  class M;\n"
      "    int v = 4;\n"
      "    function new(int a = 4); v = a; endfunction\n"
      "    static function M by_return(); return new(7); endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module t;\n"
      "  import p::*;\n"
      "  function M mk_return(); return new; endfunction\n"
      "  M m, s;\n"
      "  initial begin\n"
      "    m = mk_return(); s = M::by_return();\n"
      "    $display(\"%0d %0d %0d %0d\", m == null, s == null, m.v, s.v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "0 0 4 7\n");
}

// §13.4.1 (printed page 342) with §8.3: the implicit variable is the
// function's own, of its return type, so a call of another function of the
// same name made while the body runs -- B's make, returning a B -- leaves the
// outer make's variable an A, and `$cast(make, a)` casts an A into it and
// succeeds. Recorded under the bare name for the whole run, the inner call's
// class stood for the outer's variable, the cast failed and the call
// returned null.
TEST(FunctionReturnSim, ReturnVariableClassOutlivesANestedSameNamedCall) {
  SimFixture f;
  std::string out = RunCapture(
      "class A; int v = 1; endclass\n"
      "class B; int v = 2; static function B make(); make = new; endfunction\n"
      "endclass\n"
      "class F;\n"
      "  static int ok = 0;\n"
      "  static function A make();\n"
      "    A a = new;\n"
      "    B inner = B::make();\n"
      "    ok = $cast(make, a);\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  A r;\n"
      "  initial begin\n"
      "    r = F::make();\n"
      "    $display(\"%0d %0d\", r == null, F::ok);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "0 1\n");
}

}  // namespace
