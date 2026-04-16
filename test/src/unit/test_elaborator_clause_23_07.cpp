#include "fixture_elaborator.h"

namespace {

// --- Rule (a): First component resolves to a data object ---

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

// --- Rule (b): First component resolves to a directly visible scope name ---

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

// --- Rules (a) and (b) coexist: same module uses both member selects and
//     hierarchical names ---

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

// --- Rule (d): First component not found → treated as hierarchical name ---

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

}  // namespace
