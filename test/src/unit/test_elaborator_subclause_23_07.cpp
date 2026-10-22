#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(DottedNameElaboration, StructDataObjectIsMemberSelect) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } pair_t;\n"
      "  pair_t s;\n"
      "  logic [7:0] result;\n"
      "  initial result = s.x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, UnionDataObjectIsMemberSelect) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union packed { logic [7:0] a; logic [7:0] b; } u_t;\n"
      "  u_t u;\n"
      "  logic [7:0] result;\n"
      "  initial result = u.a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, ClassDataObjectIsMemberSelect) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class C;\n"
      "    int val;\n"
      "  endclass\n"
      "  C obj;\n"
      "  int result;\n"
      "  initial begin\n"
      "    obj = new;\n"
      "    result = obj.val;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, NestedStructMemberSelect) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; } inner_t;\n"
      "  typedef struct packed { inner_t sub; } outer_t;\n"
      "  outer_t o;\n"
      "  logic [7:0] result;\n"
      "  initial result = o.sub.x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §23.7 rule a): the first component may resolve to an interface port as well
// as to a data object. When it names an interface port, the dotted name is a
// select of that port's member, not a hierarchical name. Production resolves
// the port-rooted dotted name against the interface's declaration and accepts
// the member select.
TEST(DottedNameElaboration, InterfacePortIsMemberSelect) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_if;\n"
      "  logic [7:0] data;\n"
      "endinterface\n"
      "module sub(simple_if vif);\n"
      "  logic [7:0] r;\n"
      "  initial r = vif.data;\n"
      "endmodule\n"
      "module t;\n"
      "  simple_if intf();\n"
      "  sub u(intf);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §23.7: the distinguishing aspect between a member select and a hierarchical
// name is what the first component names. An interface *port* name roots a
// member select (rule a, covered above), but an interface *instance* is a
// scope name, so a dotted name rooted at it is a hierarchical name (rule b).
// This is the contrasting half of InterfacePortIsMemberSelect: the same
// interface's member is reached, but through an instance rather than a port,
// and production resolves it as a hierarchical reference into the instance
// rather than a select of a data object.
TEST(DottedNameElaboration, InterfaceInstanceScopeIsHierarchicalName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_if;\n"
      "  logic [7:0] data;\n"
      "endinterface\n"
      "module t;\n"
      "  simple_if intf();\n"
      "  logic [7:0] result;\n"
      "  initial result = intf.data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, InstanceScopeIsHierarchicalName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic [7:0] sig;\n"
      "endmodule\n"
      "module t;\n"
      "  child c1();\n"
      "  logic [7:0] result;\n"
      "  initial result = c1.sig;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, MultiLevelScopeIsHierarchicalName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf;\n"
      "  logic [7:0] data;\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l1();\n"
      "endmodule\n"
      "module t;\n"
      "  mid m1();\n"
      "  logic [7:0] result;\n"
      "  initial result = m1.l1.data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, MemberSelectAndHierarchicalNameCoexist) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic [7:0] sig;\n"
      "endmodule\n"
      "module t;\n"
      "  child c1();\n"
      "  typedef struct packed { logic [7:0] x; } s_t;\n"
      "  s_t s;\n"
      "  logic [7:0] r1, r2;\n"
      "  initial begin\n"
      "    r1 = s.x;\n"
      "    r2 = c1.sig;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DottedNameElaboration, UnresolvedFirstComponentTreatedAsHierarchical) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = unknown_scope.sig;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical name 'unknown_scope' resolves to no declaration", 3,
      "23.8"));
}

// §23.7: when the first component of a dotted name resolves to a name brought
// into scope by a package import (an imported scope name), the dotted name is
// resolved as a hierarchical name, as though it were prefixed by the package
// the name was imported from. The imported root is therefore accepted as a
// hierarchical reference rather than rejected as an unknown member select.
TEST(DottedNameElaboration, ImportedScopeNameTreatedAsHierarchical) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  function automatic int f();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  import p::*;\n"
      "  int result;\n"
      "  initial result = f.x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// §23.7 rule a): the classification of a dotted name as a member select does
// not depend on whether it appears as a source or a target. A dotted name
// rooted at a struct data object on the left-hand side of an assignment is
// still resolved as a member select, and elaboration accepts the write.
TEST(DottedNameElaboration, StructMemberSelectAsAssignmentTarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } pair_t;\n"
      "  pair_t s;\n"
      "  initial s.x = 8'h12;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §23.7 rule b): likewise, a dotted name rooted at a directly visible scope
// name is resolved as a hierarchical name in target position. Assigning through
// an instance-scoped hierarchical name elaborates without rejecting the name as
// a member select.
TEST(DottedNameElaboration, HierarchicalNameAsAssignmentTarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  logic [7:0] sig;\n"
      "endmodule\n"
      "module t;\n"
      "  child c1();\n"
      "  initial c1.sig = 8'h34;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §23.7 a) with §6.11 and §6.12: a dotted name whose first component is a
// variable of an integral or a real type selects from that variable, and
// neither type has a member or a built-in method, so a call through it, a
// member read through it and a call through an element of an integral array
// each name nothing.
TEST(DottedNameElaboration, SelectThroughAnIntegralOrRealVariableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  real r;\n"
      "  logic [7:0] v [2];\n"
      "  shortreal sr;\n"
      "  realtime rt;\n"
      "  initial begin\n"
      "    x.run();\n"
      "    $display(r.h);\n"
      "    v[0].go();\n"
      "    $display(sr.h, rt.h);\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* noun = "built-in method of the integral or real value";
  for (int line : {8, 9, 10, 11}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), noun, line, "23.7"))
        << line;
  }
}

// §18.8: a random property of a class has rand_mode, an integral one among
// them, so calling it is no select through an integral value.
TEST(DottedNameElaboration, RandModeOfARandomIntegralPropertyIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class c;\n"
      "  rand int x;\n"
      "  function void off(); x.rand_mode(0); endfunction\n"
      "endclass\n"
      "module top;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §23.7 a) with §7.2: a dotted name whose first name is a variable of a
// structure type is a member select, which names one of the members the type
// declares.
TEST(DottedNameElaboration, SelectOfAnUndeclaredStructMemberIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int i; int j; } st;\n"
      "  st s;\n"
      "  int x;\n"
      "  initial x = s.zz;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure 'st' has no member named 'zz'", 5,
                            "23.7"));
}

// The member a select names is looked for in the type reached at that point:
// an element of an array of structures, the inline structure a member is
// declared with, and the union type a member is declared with by its name.
TEST(DottedNameElaboration, SelectOfAnUndeclaredNestedMemberIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef union { int a; shortint b; } u_t;\n"
      "  typedef struct { struct { int k; } n; u_t u; } st;\n"
      "  st s [2];\n"
      "  int x, y;\n"
      "  initial x = s[1].n.zz;\n"
      "  initial y = s[0].u.c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the structure of 'n' has no member named 'zz'", 6,
                            "23.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "union 'u_t' has no member named 'c'", 7, "23.7"));
}

// The members declared reach as far as a select names them: an element of an
// unpacked array of structures, a member of an inline structure and of a
// union type, a structure variable of a package, and an element of a packed
// array of packed structures, which no unpacked select reaches.
TEST(DottedNameElaboration, SelectsOfDeclaredStructMembersAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  typedef struct { int i; } pt;\n"
      "  pt v;\n"
      "endpackage\n"
      "module m;\n"
      "  typedef union { int a; shortint b; } u_t;\n"
      "  typedef struct { int i; struct { int k; } n; u_t u; } st;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } ps;\n"
      "  st s [2];\n"
      "  ps [1:0] pa;\n"
      "  int w, x, y, z;\n"
      "  logic [3:0] q;\n"
      "  initial begin\n"
      "    w = p::v.i;\n"
      "    x = s[0].i;\n"
      "    y = s[1].n.k;\n"
      "    z = s[0].u.b;\n"
      "    q = pa[1].a;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §27.5 makes a generate block a scope of its own: the type a variable or a
// formal declared in it names is the block's typedef of that name, which
// stands over the module's (§23.9), and else the module's.
TEST(DottedNameElaboration, GenerateBlockSelectReadsTheBlocksTypedef) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; } pair_t;\n"
      "  typedef struct { int k; } st;\n"
      "  if (1) begin : g\n"
      "    typedef struct { int a, b; } pair_t;\n"
      "    st s;\n"
      "    function int f(pair_t p);\n"
      "      return p.a + p.b;\n"
      "    endfunction\n"
      "    int x;\n"
      "    initial x = s.zz;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure 'st' has no member named 'zz'", 11,
                            "23.7"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "structure 'pair_t' has no member named 'b'", 8,
                             "23.7"));
}

// §23.9 makes a task, a function and a begin-end block each a scope, whose
// own typedef of a name stands over the module's (§6.18): the type a
// variable declared there names is the scope's own, and else the type of the
// scope around it, a block inside a function seeing the function's.
TEST(DottedNameElaboration, SubroutineAndBlockSelectsReadTheirOwnTypedefs) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; } pair_t;\n"
      "  function int f();\n"
      "    typedef struct { int a, b; } pair_t;\n"
      "    pair_t p;\n"
      "    return p.b;\n"
      "  endfunction\n"
      "  function int g();\n"
      "    typedef struct { int k; } q_t;\n"
      "    q_t q;\n"
      "    begin\n"
      "      q_t r;\n"
      "      return q.zz + r.yy;\n"
      "    end\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial begin\n"
      "    typedef struct { int k; } s_t;\n"
      "    s_t s;\n"
      "    x = s.ww;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "structure 'pair_t' has no member named 'b'", 6,
                             "23.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure 'q_t' has no member named 'zz'", 13,
                            "23.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure 'q_t' has no member named 'yy'", 13,
                            "23.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "structure 's_t' has no member named 'ww'", 20,
                            "23.7"));
}

// What follows a member declared with a class type is a property of the class
// (§8), as what follows a property of a class handle is, and a random
// structure property of a class has rand_mode (§18.8): none of them is a
// member of the structure. Nor is a property of a structure type the class
// declares for itself read as one.
TEST(DottedNameElaboration, ClassMemberAndRandModeOfAStructAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "class k;\n"
      "  int v;\n"
      "endclass\n"
      "class j;\n"
      "  k h;\n"
      "endclass\n"
      "module m;\n"
      "  typedef struct { int i; } r_t;\n"
      "  class c;\n"
      "    typedef struct { int i; } q_t;\n"
      "    rand r_t r;\n"
      "    q_t q;\n"
      "    function void off(); r.rand_mode(0); endfunction\n"
      "    function int get(); return q.i; endfunction\n"
      "  endclass\n"
      "  typedef struct { int i; k h; } st;\n"
      "  st s;\n"
      "  j g;\n"
      "  int x, y;\n"
      "  initial x = s.h.v;\n"
      "  initial y = g.h.v;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
