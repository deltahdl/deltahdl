#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "<abcdef> <abcdef>\n");
}

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

TEST(FunctionReturnSim, ArrayReturnedByACallIsAssignedElementForElement) {
  SimFixture f;
  auto out = RunCapture(
      "class K;\n"
      "  typedef int q_t[$];\n"
      "  q_t hold;\n"
      "  function q_t get(); q_t v; v.push_back(11); v.push_back(12); "
      "return v; endfunction\n"
      "  function void keep(); hold = get(); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  typedef int a_t[3];\n"
      "  typedef int q_t[$];\n"
      "  int n;\n"
      "  function automatic a_t fa(); a_t v; n++; v[0] = 7; v[1] = 8; "
      "v[2] = 9; return v; endfunction\n"
      "  function automatic q_t fq(); q_t v; v.push_back(4); v.push_back(5); "
      "return v; endfunction\n"
      "  a_t av; int r[2:0]; q_t qv; int kq[$];\n"
      "  K k;\n"
      "  initial begin\n"
      "    av = fa(); r = fa(); qv = fq(); k = new; kq = k.get(); k.keep();\n"
      "    $display(\"%p %p %p %p %0d n=%0d\", av, r, qv, kq, k.hold[1], n);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{7, 8, 9} '{7, 8, 9} '{4, 5} '{11, 12} 12 n=2\n");
}

TEST(FunctionReturnSim, MemberOfAnElementOfAnArrayValuedCall) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef struct {int x; int y;} s_t;\n"
      "  typedef s_t q_t[$];\n"
      "  typedef s_t a_t[2];\n"
      "  function automatic q_t mk(); q_t v; v.push_back('{4, 40}); "
      "v.push_back('{5, 50}); return v; endfunction\n"
      "  function automatic a_t mka(); a_t v; v[0] = '{4, 40}; "
      "v[1] = '{5, 50}; return v; endfunction\n"
      "  s_t sq[$];\n"
      "  initial begin\n"
      "    sq = '{'{1, 10}, '{3, 30}};\n"
      "    $display(\"%0d %0d %0d %0d\", mk()[1].y, mka()[0].x, mka()[1].y,\n"
      "             sq.find(i) with (i.x == 3) [0].y);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "50 4 50 30\n");
}

TEST(FunctionReturnSim, ImplicitVariableOfAnArrayReturnTypeIsAnArray) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef int a_t[3];\n"
      "  typedef int q_t[$];\n"
      "  typedef struct {int x; int y;} s_t;\n"
      "  typedef s_t sa_t[2];\n"
      "  function automatic a_t fn(); fn[0] = 7; fn[1] = 8; fn[2] = 9; "
      "endfunction\n"
      "  function automatic a_t fp(); return '{7, 8, 9}; endfunction\n"
      "  function automatic a_t fw(); return fp(); endfunction\n"
      "  function automatic q_t qn(); qn.push_back(4); qn.push_back(5); "
      "endfunction\n"
      "  function automatic q_t qp(); return '{4, 5}; endfunction\n"
      "  function automatic a_t early(int k); early = '{1, 1, 1};\n"
      "    if (k) return '{2, 2, 2}; early[0] = 3; endfunction\n"
      "  function automatic sa_t mk(); mk[0].x = 4; mk[1].y = 50; "
      "endfunction\n"
      "  a_t av; q_t qv;\n"
      "  initial begin\n"
      "    $write(\"%0d %0d %0d %0d \", fn()[1], fp()[2], qn().size(), "
      "qp()[1]);\n"
      "    av = fw(); qv = qn();\n"
      "    $write(\"%p %p \", av, qv);\n"
      "    av = early(1); $write(\"%p \", av); av = early(0);\n"
      "    $display(\"%p %0d\", av, mk()[1].y);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8 9 2 5 '{7, 8, 9} '{4, 5} '{2, 2, 2} '{3, 1, 1} 50\n");
}

TEST(FunctionReturnSim, InstanceMethodReturnRangeNamesClassConstants) {
  SimFixture f;
  std::string out = RunCapture(
      "class C #(int N = 3);\n"
      "  localparam int M = N + 1;\n"
      "  function logic [N-1:0] g(); return '1; endfunction\n"
      "  function logic [N-1:0] g2(); g2 = 5; endfunction\n"
      "  function logic [M-1:0] gm(); return '1; endfunction\n"
      "endclass\n"
      "class D;\n"
      "  localparam int K = 5;\n"
      "  function logic [K-1:0] d(); return '1; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    automatic C #(6) c = new;\n"
      "    automatic C c3 = new;\n"
      "    automatic D d = new;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", c.g(), c.g2(), c.gm(), c3.g(),\n"
      "             d.d());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "63 5 127 7 31\n");
}

TEST(FunctionReturnSim, FunctionNameWithoutParenthesesIsAScope) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "class A;\n"
      "  int member = 1;\n"
      "endclass\n"
      "module top;\n"
      "  A a;\n"
      "  function A F;\n"
      "    int member;\n"
      "    a = new();\n"
      "    return a;\n"
      "  endfunction\n"
      "  int r;\n"
      "  initial r = F.member * 10 + F().member;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 1u);
}

TEST(FunctionReturnSim, SelectOnACallUsesTheReturnTypesRange) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module m;\n"
      "  function bit [15:10] g(); return 6'b101101; endfunction\n"
      "  bit [3:0] r;\n"
      "  bit b;\n"
      "  int n;\n"
      "  initial begin\n"
      "    r = g()[13:10];\n"
      "    b = g()[15];\n"
      "    n = r * 10 + b;\n"
      "  end\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 131u);
}

std::string SignedReturns(const char* fb, const char* fs, const char* fh,
                          const char* fa) {
  return std::string("module m;\n  int a, b, c, d;\n") +
         "  function byte fb(); " + fb + " endfunction\n" +
         "  function signed [7:0] fs(); " + fs + " endfunction\n" +
         "  function shortint fh(); " + fh + " endfunction\n" +
         "  function automatic logic signed [7:0] fa(); " + fa +
         " endfunction\n"
         "  initial begin\n"
         "    a = fb(); b = fs(); c = fh(); d = fa();\n"
         "    $display(\"%0d %0d %0d %0d %0d\", a, b, c, d, fs() < 0);\n"
         "  end\n"
         "endmodule\n";
}

TEST(FunctionReturnSim, ASignedValueReturnedByAReturnStatementKeepsItsSign) {
  SimFixture f;
  EXPECT_EQ(RunCapture(SignedReturns("return 8'h80;", "return 8'h80;",
                                     "return 16'h8000;", "return 8'h80;"),
                       f),
            "-128 -128 -32768 -128 1\n");
}

TEST(FunctionReturnSim,
     DISABLED_ASignedValueAssignedToTheFunctionNameKeepsItsSign) {
  SimFixture f;
  EXPECT_EQ(RunCapture(SignedReturns("fb = 8'h80;", "fs = 8'h80;",
                                     "fh = 16'h8000;", "fa = 8'h80;"),
                       f),
            "-128 -128 -32768 -128 1\n");
}

}  // namespace
