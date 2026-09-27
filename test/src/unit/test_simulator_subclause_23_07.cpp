#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(DottedNameSimulation, StructMemberSelectReadsField) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } pair_t;\n"
      "  pair_t s;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    s = 16'hAB_CD;\n"
      "    result = s.x;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0xABu);
}

TEST(DottedNameSimulation, StructMemberSelectWritesField) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t s;\n"
      "  initial begin\n"
      "    s = 16'h0000;\n"
      "    s.hi = 8'hFF;\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0xFF00u);
}

TEST(DottedNameSimulation, UnionMemberSelectReadsField) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef union packed { logic [7:0] a; logic [7:0] b; } u_t;\n"
      "  u_t u;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    u.a = 8'h42;\n"
      "    result = u.b;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0x42u);
}

TEST(DottedNameSimulation, ClassMemberSelectReadsProperty) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    int val;\n"
      "    function new;\n"
      "      val = 99;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial begin\n"
      "    C obj;\n"
      "    obj = new;\n"
      "    result = obj.val;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 99u);
}

TEST(DottedNameSimulation, NestedStructMemberSelectReadsDeepField) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; } inner_t;\n"
      "  typedef struct packed { inner_t sub; } outer_t;\n"
      "  outer_t o;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    o.sub.x = 8'h77;\n"
      "    result = o.sub.x;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0x77u);
}

TEST(DottedNameSimulation, InstanceScopeReadsHierarchicalName) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module child;\n"
      "  logic [7:0] val;\n"
      "  initial val = 8'd42;\n"
      "endmodule\n"
      "module t;\n"
      "  child c1();\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    #1;\n"
      "    result = c1.val;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
}

TEST(DottedNameSimulation, InstanceScopeWritesHierarchicalName) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module child;\n"
      "  logic [7:0] val;\n"
      "endmodule\n"
      "module t;\n"
      "  child c1();\n"
      "  initial c1.val = 8'd55;\n"
      "endmodule\n",
      f, "c1.val");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 55u);
}

TEST(DottedNameSimulation, MemberSelectAndHierarchicalNameInSameModule) {
  SimFixture f;
  auto* v1 = RunAndFindVar(
      "module child;\n"
      "  logic [7:0] sig;\n"
      "  initial sig = 8'd10;\n"
      "endmodule\n"
      "module t;\n"
      "  child c1();\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } pair_t;\n"
      "  pair_t s;\n"
      "  logic [7:0] r1, r2;\n"
      "  initial begin\n"
      "    s = 16'h00_33;\n"
      "    r1 = s.y;\n"
      "    #1;\n"
      "    r2 = c1.sig;\n"
      "  end\n"
      "endmodule\n",
      f, "r1");
  ASSERT_NE(v1, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 0x33u);
  auto* v2 = f.ctx.FindVariable("r2");
  ASSERT_NE(v2, nullptr);
  EXPECT_EQ(v2->value.ToUint64(), 10u);
}

// §23.7 rule b at run time, exercised through the interface (§25) dependency
// end-to-end: an interface instance is a directly visible scope name, so a
// dotted name rooted at it is a hierarchical name rather than a member select.
// The interface is built from real source syntax and driven through the whole
// pipeline; the parent writes and then reads the interface's variable through
// the instance-rooted hierarchical name, and the resolved reference carries the
// value at run time. This is the interface-instance scope-kind form of the
// hierarchical-name rule, complementing the module-instance forms above.
TEST(DottedNameSimulation,
     InterfaceInstanceScopeReadsAndWritesHierarchicalName) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "interface simple_if;\n"
      "  logic [7:0] data;\n"
      "endinterface\n"
      "module t;\n"
      "  simple_if intf();\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    intf.data = 8'h5A;\n"
      "    result = intf.data;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0x5Au);
}

// §23.7 (printed pages 757-758): a dotted name whose first component resolves
// to a subroutine is a hierarchical name into it, so `f.x` is the static
// variable x of the function f -- here one imported from a package, the
// standard's own example's `f.x = 3` making `p::f()` return 3. The write went
// nowhere: the static local existed only once a call had declared it, and
// nothing looked a dotted name up among a function's locals.
TEST(DottedNameResolution, DottedNameWritesAnImportedFunctionsStaticLocal) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  function int f();\n"
                       "    static int x = 0;\n"
                       "    return x;\n"
                       "  endfunction\n"
                       "endpackage\n"
                       "module top;\n"
                       "  import p::*;\n"
                       "  initial begin\n"
                       "    f.x = 3;\n"
                       "    #1 $display(\"%0d %0d\", p::f(), f());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3 3\n");
}

// A read reaches the variable the calls keep: after two calls that count x
// up, `p::f.x` and the module's own `g.y` read what the calls left there.
TEST(DottedNameResolution, DottedNameReadsTheStaticLocalTheCallsKeep) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  function int f();\n"
                       "    static int x = 0;\n"
                       "    x = x + 1;\n"
                       "    return x;\n"
                       "  endfunction\n"
                       "endpackage\n"
                       "module top;\n"
                       "  import p::*;\n"
                       "  function int g();\n"
                       "    static int y = 10;\n"
                       "    y = y + 5;\n"
                       "    return y;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    $display(\"%0d %0d %0d\", p::f(), f(), p::f.x);\n"
                       "    g.y = 1;\n"
                       "    $display(\"%0d %0d\", g(), g.y);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 2 2\n6 6\n");
}

}  // namespace
