#include <gtest/gtest.h>

#include <string>

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

// §23.7 with §6.21: a static local written with no initializer is not made
// before the procedures start as one with an initializer is (§10.5), so
// `f.x = 4` ahead of any call makes it in the function's static frame, where
// the call then reads it.
TEST(DottedNameResolution, DottedNameWritesAStaticLocalNoCallHasMade) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  function int f();\n"
                       "    static int x;\n"
                       "    return x;\n"
                       "  endfunction\n"
                       "endpackage\n"
                       "module top;\n"
                       "  import p::*;\n"
                       "  initial begin\n"
                       "    f.x = 4;\n"
                       "    #1 $display(\"%0d\", f());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "4\n");
}

// §23.7 rule c): a dotted name whose first name is a scope a package import
// brings in, `f.x` with `import p::*`, is the hierarchical name behind the
// package's name, `p::f.x`. A function declared in a package or a module is
// static (§13.4.2), so its local is static though `static` is not written, and
// the name reaches that one variable: written before any call, read after
// calls that count in it, and the same through a module's own function,
// whose automatic local and parameter the name passes over.
TEST(DottedNameSimulation, NameThroughAStaticFunctionReachesItsLocal) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  function int f();\n"
                       "    int x;\n"
                       "    x = x + 1;\n"
                       "    return x;\n"
                       "  endfunction\n"
                       "endpackage\n"
                       "module m;\n"
                       "  import p::*;\n"
                       "  function int mc();\n"
                       "    automatic int t;\n"
                       "    parameter int K = 1;\n"
                       "    int c;\n"
                       "    t = K;\n"
                       "    c = c + t;\n"
                       "    return c;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    f.x = 3;\n"
                       "    $display(\"%0d %0d\", f.x, p::f.x);\n"
                       "    void'(f());\n"
                       "    $display(\"%0d %0d\", p::f(), p::f.x);\n"
                       "    void'(mc());\n"
                       "    $display(\"%0d %0d\", mc(), mc.c);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3 3\n5 5\n2 2\n");
}

// §23.7's dotted name 2 (printed pages 757-758): `s2.x` written in a generate
// block before the block's instance s2 resolves its first name where it
// stands, where only the structure p::s2 the module imports is visible, so
// the write reaches p::s2.x and the instance's x keeps its value.
TEST(DottedNameResolution, DottedNameBeforeAnInstanceWritesTheImportedStruct) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  struct { int x; } s2;\n"
                       "endpackage\n"
                       "module some_module;\n"
                       "  int x;\n"
                       "endmodule\n"
                       "module m;\n"
                       "  import p::*;\n"
                       "  if (1) begin : s1\n"
                       "    initial begin\n"
                       "      s2.x = 2;\n"
                       "      #1 $display(\"%0d %0d\", p::s2.x, s1.s2.x);\n"
                       "    end\n"
                       "    some_module s2();\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "2 0\n");
  EXPECT_FALSE(f.has_errors);
}

// §23.7 with §26.3: the binding holds for a read standing in a block nested
// inside the one declaring the instance after it, which reads p::s2.x's 7,
// while a read after a block's instance reaches the instance's x, 3.
TEST(DottedNameResolution, NestedReadBeforeAnInstanceReadsTheImportedStruct) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  struct { int x; } s2;\n"
                       "endpackage\n"
                       "module some_module;\n"
                       "  int x = 3;\n"
                       "endmodule\n"
                       "module m;\n"
                       "  import p::*;\n"
                       "  initial p::s2.x = 7;\n"
                       "  if (1) begin : o\n"
                       "    if (1) begin : i\n"
                       "      initial #1 $display(\"%0d\", s2.x);\n"
                       "    end\n"
                       "    some_module s2();\n"
                       "  end\n"
                       "  if (1) begin : a\n"
                       "    some_module s2();\n"
                       "    initial #2 $display(\"%0d\", s2.x);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "7\n3\n");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
