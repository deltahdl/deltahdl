// §18.5: Constraint blocks

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A2ClassWithConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c1 { x > 0; x < 100; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

using CheckerParseTest = ProgramTestParse;

// class_item ::= { attribute_instance } class_constraint
TEST(SourceText, ClassConstraint) {
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "  constraint c1 { x > 0; }\n"
      "  constraint c2;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 3u);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kConstraint);
  EXPECT_EQ(members[1]->name, "c1");
  EXPECT_EQ(members[2]->kind, ClassMemberKind::kConstraint);
  EXPECT_EQ(members[2]->name, "c2");
}

// =============================================================================
// A.1.10 Constraints
// =============================================================================
// constraint_declaration ::=
//   [static] constraint [dynamic_override_specifiers] constraint_identifier
//   constraint_block
TEST(SourceText, ConstraintDeclaration) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c1 { x > 0; }\n"
      "  static constraint c2 { x < 100; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_GE(members.size(), 3u);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kConstraint);
  EXPECT_EQ(members[1]->name, "c1");
  EXPECT_FALSE(members[1]->is_static);
  EXPECT_EQ(members[2]->kind, ClassMemberKind::kConstraint);
  EXPECT_EQ(members[2]->name, "c2");
  EXPECT_TRUE(members[2]->is_static);
}

// constraint_block ::= { { constraint_block_item } }
// constraint_block_item ::= solve ... before ... ; | constraint_expression
TEST(SourceText, ConstraintBlockItems) {
  auto r = Parse(
      "class C;\n"
      "  rand int a;\n"
      "  rand int b;\n"
      "  rand int c;\n"
      "  constraint order_c {\n"
      "    solve a before b;\n"
      "    solve a before b, c;\n"
      "    a > 0;\n"
      "    soft b == 1;\n"
      "    a > 0 -> b < 10;\n"
      "    if (a > 5) { b == 1; } else { b == 0; }\n"
      "    foreach (c[i]) c[i] > 0;\n"
      "    disable soft a;\n"
      "    unique { a, b, c };\n"
      "  }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_GE(members.size(), 4u);
  EXPECT_EQ(members[3]->kind, ClassMemberKind::kConstraint);
  EXPECT_EQ(members[3]->name, "order_c");
}

TEST(ParserSection8, ClassWithConstraint) {
  auto r = Parse(
      "class Constrained;\n"
      "  rand int x;\n"
      "  constraint c1 { x > 0; x < 100; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  bool found = false;
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kConstraint) {
      found = true;
      EXPECT_EQ(m->name, "c1");
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
