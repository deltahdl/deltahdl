#include "fixture_elaborator.h"

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

}  // namespace
