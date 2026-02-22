// §18.5: Constraint blocks

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

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
  auto &members = r.cu->classes[0]->members;
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
  auto &members = r.cu->classes[0]->members;
  ASSERT_GE(members.size(), 3u);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kConstraint);
  EXPECT_EQ(members[1]->name, "c1");
  EXPECT_FALSE(members[1]->is_static);
  EXPECT_EQ(members[2]->kind, ClassMemberKind::kConstraint);
  EXPECT_EQ(members[2]->name, "c2");
  EXPECT_TRUE(members[2]->is_static);
}

// constraint_declaration with dynamic_override_specifiers (§8.20)
TEST(SourceText, ConstraintDeclDynamicOverride) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint :initial c1 { x > 0; }\n"
      "  constraint :extends c2 { x < 100; }\n"
      "  constraint :final c3 { x == 42; }\n"
      "  constraint :initial :final c4 { x != 0; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto &members = r.cu->classes[0]->members;
  ASSERT_GE(members.size(), 5u);
  EXPECT_EQ(members[1]->name, "c1");
  EXPECT_EQ(members[2]->name, "c2");
  EXPECT_EQ(members[3]->name, "c3");
  EXPECT_EQ(members[4]->name, "c4");
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
  auto &members = r.cu->classes[0]->members;
  ASSERT_GE(members.size(), 4u);
  EXPECT_EQ(members[3]->kind, ClassMemberKind::kConstraint);
  EXPECT_EQ(members[3]->name, "order_c");
}

// constraint_expression ::= expression_or_dist ;
// expression_or_dist ::= expression [ dist { dist_list } ]
// dist_list ::= dist_item { , dist_item }
// dist_item ::= value_range [ dist_weight ] | default :/ expression
// dist_weight ::= := expression | :/ expression
TEST(SourceText, ConstraintExpressionOrDist) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint dist_c {\n"
      "    x dist { 1 := 10, [2:5] :/ 20, default :/ 1 };\n"
      "  }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[1]->name, "dist_c");
}

// constraint_set ::= constraint_expression | { { constraint_expression } }
TEST(SourceText, ConstraintSet) {
  auto r = Parse(
      "class C;\n"
      "  rand int a;\n"
      "  rand int b;\n"
      "  constraint cs {\n"
      "    if (a > 0) b > 0;\n"
      "    if (a > 10) { b > 10; b < 100; }\n"
      "  }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[2]->name, "cs");
}

// constraint_prototype ::=
//   [constraint_prototype_qualifier] [static] constraint
//   [dynamic_override_specifiers] constraint_identifier ;
// constraint_prototype_qualifier ::= extern | pure
TEST(SourceText, ConstraintPrototype) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint c1;\n"
      "  pure constraint c2;\n"
      "  extern static constraint c3;\n"
      "  constraint c4;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto &members = r.cu->classes[0]->members;
  ASSERT_GE(members.size(), 5u);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kConstraint);
  EXPECT_EQ(members[1]->name, "c1");
  EXPECT_EQ(members[2]->name, "c2");
  EXPECT_EQ(members[3]->name, "c3");
  EXPECT_TRUE(members[3]->is_static);
  EXPECT_EQ(members[4]->name, "c4");
}

// constraint_prototype with dynamic_override_specifiers
TEST(SourceText, ConstraintPrototypeDynamicOverride) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint :initial c1;\n"
      "  pure constraint :final c2;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto &members = r.cu->classes[0]->members;
  ASSERT_GE(members.size(), 3u);
  EXPECT_EQ(members[1]->name, "c1");
  EXPECT_EQ(members[2]->name, "c2");
}

// extern_constraint_declaration ::=
//   [static] constraint [dynamic_override_specifiers] class_scope
//   constraint_identifier constraint_block
TEST(SourceText, ExternConstraintDeclaration) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint c;\n"
      "endclass\n"
      "constraint C::c { x > 0; }\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// extern_constraint_declaration with static and dynamic_override_specifiers
TEST(SourceText, ExternConstraintDeclStaticOverride) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern static constraint c;\n"
      "endclass\n"
      "static constraint C::c { x > 0; }\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// extern_constraint_declaration with dynamic_override_specifiers at top-level
TEST(SourceText, ExternConstraintDeclDynOverrideTopLevel) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint c;\n"
      "endclass\n"
      "constraint :initial C::c { x > 0; }\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// uniqueness_constraint ::= unique { range_list }
TEST(SourceText, UniquenessConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int a;\n"
      "  rand int b;\n"
      "  rand int c;\n"
      "  constraint uc { unique { a, b, c }; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[3]->name, "uc");
}

// Constraint with foreach and nested constraint_set
TEST(SourceText, ConstraintForeach) {
  auto r = Parse(
      "class C;\n"
      "  rand int arr[10];\n"
      "  constraint fc {\n"
      "    foreach (arr[i]) {\n"
      "      arr[i] inside {[0:100]};\n"
      "    }\n"
      "  }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[1]->name, "fc");
}

// Constraint implication and disable soft
TEST(SourceText, ConstraintImplicationDisableSoft) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint ic {\n"
      "    x > 0 -> y > 0;\n"
      "    disable soft x;\n"
      "  }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[2]->name, "ic");
}

// Footnote 11: dynamic_override_specifiers illegal with static (semantic, not
// syntactic) — parser still accepts for later semantic check
TEST(SourceText, ConstraintFootnote11StaticWithOverride) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  static constraint :initial c1 { x > 0; }\n"
      "endclass\n");
  // Parser should accept; footnote 11 is a semantic restriction
  ASSERT_FALSE(r.has_errors);
}

}  // namespace
