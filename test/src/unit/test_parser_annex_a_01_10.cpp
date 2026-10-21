#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_class.h"

using namespace delta;

namespace {

TEST(ConstraintItemsParsing, BasicConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c_x { x > 0; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, SolveBefore) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  constraint c { solve x before y; x inside {[0:10]}; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, SoftConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c_x { soft x == 5; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, ImplicationConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  constraint c { x > 0 -> y > 0; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, IfElseConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, mode;\n"
      "  constraint c {\n"
      "    if (mode == 0) { x < 10; }\n"
      "    else { x > 100; }\n"
      "  }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, DisableSoft) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c_x { soft x == 5; }\n"
      "  constraint c_override { disable soft x; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, DistConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c_x {\n"
      "    x dist { 1 := 10, [2:5] :/ 20 };\n"
      "  }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, MultipleConstraints) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  constraint c_x { x > 0; }\n"
      "  constraint c_y { y > 0; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->classes[0]->members.size(), 4u);
}

TEST(ConstraintItemsParsing, EmptyConstraintBlock) {
  auto r = Parse(
      "class C;\n"
      "  constraint c_empty { }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, InsideConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c_x { x inside {1, 2, [5:10]}; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, ConstraintDeclarationAndPrototype) {
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

TEST(ConstraintItemsParsing, StaticConstraintVerified) {
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

TEST(ConstraintItemsParsing, ConstraintBlockItems) {
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

TEST(ConstraintItemsParsing, ClassWithConstraintVerifiesName) {
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

TEST(ConstraintItemsParsing, PackageItemExternConstraint) {
  auto r = Parse(
      "package pkg;\n"
      "  constraint MyClass::c { x > 0; }\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(ConstraintItemsParsing, ConstraintPrototypeQualifiers) {
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
  auto& members = r.cu->classes[0]->members;
  ASSERT_GE(members.size(), 5u);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kConstraint);
  EXPECT_EQ(members[1]->name, "c1");
  EXPECT_EQ(members[2]->name, "c2");
  EXPECT_EQ(members[3]->name, "c3");
  EXPECT_TRUE(members[3]->is_static);
  EXPECT_EQ(members[4]->name, "c4");
}

TEST(ConstraintItemsParsing, OutOfBlockConstraint) {
  auto r = Parse(
      "class a;\n"
      "  rand int b;\n"
      "  extern constraint c;\n"
      "endclass\n"
      "constraint a::c { b == 0; }\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, ConstraintDeclDynamicOverride) {
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
  auto& members = r.cu->classes[0]->members;
  ASSERT_GE(members.size(), 5u);
  EXPECT_EQ(members[1]->name, "c1");
  EXPECT_TRUE(members[1]->is_constraint_initial);
  EXPECT_FALSE(members[1]->is_constraint_extends);
  EXPECT_FALSE(members[1]->is_constraint_final);
  EXPECT_EQ(members[2]->name, "c2");
  EXPECT_FALSE(members[2]->is_constraint_initial);
  EXPECT_TRUE(members[2]->is_constraint_extends);
  EXPECT_FALSE(members[2]->is_constraint_final);
  EXPECT_EQ(members[3]->name, "c3");
  EXPECT_FALSE(members[3]->is_constraint_initial);
  EXPECT_FALSE(members[3]->is_constraint_extends);
  EXPECT_TRUE(members[3]->is_constraint_final);
  EXPECT_EQ(members[4]->name, "c4");
  EXPECT_TRUE(members[4]->is_constraint_initial);
  EXPECT_TRUE(members[4]->is_constraint_final);
}

TEST(ConstraintItemsParsing, ConstraintPrototypeDynamicOverride) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint :initial c1;\n"
      "  pure constraint :final c2;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_GE(members.size(), 3u);
  EXPECT_EQ(members[1]->name, "c1");
  EXPECT_TRUE(members[1]->is_constraint_initial);
  EXPECT_EQ(members[2]->name, "c2");
  EXPECT_TRUE(members[2]->is_constraint_final);
  EXPECT_TRUE(members[2]->is_pure_virtual);
}

TEST(ConstraintItemsParsing, ExternConstraintDeclDynOverrideTopLevel) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint c;\n"
      "endclass\n"
      "constraint :initial C::c { x > 0; }\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, DistConstraintEqualWeight) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {100:=1, 200:=2, 300:=5}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, DistConstraintDivideWeight) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {100:/1, 200:/2, 300:/5}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, DistConstraintWithRange) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[100:102]:=1, 103:=1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, DistConstraintWithDefault) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[100:102]:/3, default:/1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, DistEqualWeightSingleValue) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {42 := 1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, ConstraintExpressionOrDist) {
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

TEST(ConstraintItemsParsing, UniquenessConstraintVerifiesName) {
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

TEST(ConstraintItemsParsing, DistInsideIfConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand bit mode;\n"
      "  constraint c {\n"
      "    if (mode == 0) {\n"
      "      x dist {[0:10] := 1};\n"
      "    } else {\n"
      "      x dist {[100:200] := 1};\n"
      "    }\n"
      "  }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, ConstraintSet) {
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

TEST(ConstraintItemsParsing, ConstraintForeachBraced) {
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

TEST(ConstraintItemsParsing, ForeachConstraintSingleLine) {
  auto r = Parse(
      "class a;\n"
      "  rand int B[5];\n"
      "  constraint c { foreach (B[i]) B[i] == 5; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, PackageItemStaticExternConstraint) {
  auto r = Parse(
      "package pkg;\n"
      "  static constraint MyClass::c { x > 0; }\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(ConstraintItemsParsing, ExternConstraintDeclStaticOverride) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern static constraint c;\n"
      "endclass\n"
      "static constraint C::c { x > 0; }\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, StaticConstraintWithDynamicOverride) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  static constraint :initial c1 { x > 0; }\n"
      "endclass\n");

  ASSERT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, ImplicationAndDisableSoft) {
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

TEST(ConstraintItemsParsing, PureConstraintPrototype) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  pure constraint c;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[1]->kind, ClassMemberKind::kConstraint);
  EXPECT_EQ(r.cu->classes[0]->members[1]->name, "c");
  EXPECT_TRUE(r.cu->classes[0]->members[1]->is_pure_virtual);
}

TEST(ConstraintItemsParsing, SolveBeforeWithSelect) {
  auto r = Parse(
      "class C;\n"
      "  rand int arr[4];\n"
      "  constraint c { solve arr[0] before arr[1]; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, ForeachMultipleLoopVars) {
  auto r = Parse(
      "class C;\n"
      "  rand int matrix[3][3];\n"
      "  constraint c {\n"
      "    foreach (matrix[i, j]) matrix[i][j] > 0;\n"
      "  }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, ImplicationBracedConstraintSet) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y, z;\n"
      "  constraint c { x > 0 -> { y > 0; z > 0; } }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, NestedIfConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, c;\n"
      "  constraint nc {\n"
      "    if (a > 0) {\n"
      "      if (b > 0) {\n"
      "        c > 0;\n"
      "      }\n"
      "    }\n"
      "  }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[3]->name, "nc");
}

TEST(ConstraintItemsParsing, SoftDistConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { soft x dist { 1 := 10, 2 := 20 }; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, ErrorConstraintMissingName) {
  auto r = Parse(
      "class C;\n"
      "  constraint { x > 0; }\n"
      "endclass\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got '{'", 2, "18.5"));
}

TEST(ConstraintItemsParsing, ErrorConstraintPrototypeMissingSemicolon) {
  auto r = Parse(
      "class C;\n"
      "  constraint c\n"
      "endclass\n");
  // 'endclass' stands where the header demands the '{' that opens the block.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '{', got 'endclass'", 3, "18.5"));
}

TEST(ConstraintItemsParsing, ErrorExternConstraintMissingScope) {
  auto r = Parse("constraint c { x > 0; }\n");
  // §18.5.1 owns the external constraint block's class scope, so the '::' that
  // introduces it is what the report names as missing.
  EXPECT_TRUE(ReportedError(r.diags, "expected '::', got '{'", 1, "18.5.1"));
}

TEST(ConstraintItemsParsing, ErrorConstraintUnmatchedBrace) {
  auto r = Parse(
      "class C;\n"
      "  constraint c { x > 0;\n"
      "endclass\n");
  // The unclosed block swallows 'endclass', so §8.3 owns the report: the class
  // declaration is what runs out of source. The end of the source stands on
  // line 4, the line the trailing newline opened.
  EXPECT_TRUE(ReportedError(r.diags, "expected 'endclass', got EOF", 4, "8.3"));
}

TEST(ConstraintItemsParsing, ErrorExternConstraintMissingIdentifier) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint c;\n"
      "endclass\n"
      "constraint C:: { x > 0; }\n");
  // §18.5.1 owns the external constraint block, so its name is demanded there.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got '{'", 5, "18.5.1"));
}

TEST(ConstraintItemsParsing, MultipleConstraintBlockItems) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, c, d;\n"
      "  constraint all {\n"
      "    a > 0;\n"
      "    soft b == 1;\n"
      "    a > 5 -> { b < 10; c > 0; }\n"
      "    if (d > 0) a < 100; else a < 50;\n"
      "    foreach (c[i]) c[i] > 0;\n"
      "    unique { a, b };\n"
      "    solve a before b;\n"
      "    disable soft b;\n"
      "    a dist { [0:10] := 1, [11:100] :/ 5 };\n"
      "  }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[4]->name, "all");
}

// constraint_prototype ::= [ constraint_prototype_qualifier ] [ static ]
// constraint ...: the `extern` or `pure` stands before `static`, so
// `static extern constraint c;` is no prototype A.1.10 writes, while the
// qualifier first is one, and is still read as static (#7582).
TEST(ConstraintItemsParsing, StaticBeforePrototypeQualifierIsError) {
  auto r = Parse(
      "virtual class C;\n"
      "  rand int x;\n"
      "  static extern constraint c1;\n"
      "  static pure constraint c2;\n"
      "  extern static constraint c3;\n"
      "  pure static constraint c4;\n"
      "endclass\n");
  const char* const kMsg =
      "a constraint prototype's 'static' is written before its 'extern' or "
      "'pure'";
  EXPECT_TRUE(ReportedError(r.diags, kMsg, 3, "A.1.10"));
  EXPECT_TRUE(ReportedError(r.diags, kMsg, 4, "A.1.10"));
  EXPECT_FALSE(ReportedError(r.diags, kMsg, 5, "A.1.10"));
  EXPECT_FALSE(ReportedError(r.diags, kMsg, 6, "A.1.10"));
  ASSERT_EQ(r.cu->classes.size(), 1u);
  const auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 5u);
  EXPECT_EQ(members[1]->name, "c1");
  EXPECT_TRUE(members[1]->is_static);
  EXPECT_TRUE(members[3]->is_static);
}

// constraint_declaration ::= [ static ] constraint ... constraint_block: a
// constraint written with a block takes no qualifier but `static`, the
// constraint_prototype_qualifier being the prototype's alone (#7581).
TEST(ConstraintItemsParsing, ExternOrPureConstraintWithABlockIsError) {
  auto r = Parse(
      "virtual class C;\n"
      "  rand int x;\n"
      "  extern constraint c1 { x > 0; }\n"
      "  pure constraint c2 { x < 9; }\n"
      "  static constraint c3 { x != 5; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "'extern' is no qualifier of a constraint written with a block",
      3, "A.1.10"));
  EXPECT_TRUE(ReportedError(
      r.diags, "'pure' is no qualifier of a constraint written with a block", 4,
      "A.1.10"));
  EXPECT_FALSE(
      ReportedError(r.diags, "is no qualifier of a constraint", 5, "A.1.10"));
}

// constraint_prototype_qualifier ::= extern | pure, and a prototype takes one
// of them at most (#7583).
TEST(ConstraintItemsParsing, ExternAndPureConstraintPrototypeIsError) {
  auto r = Parse(
      "virtual class C;\n"
      "  rand int x;\n"
      "  extern pure constraint c1;\n"
      "  pure extern constraint c2;\n"
      "  pure constraint c3;\n"
      "  extern constraint c4;\n"
      "endclass\n");
  const char* const kMsg =
      "a constraint prototype takes 'extern' or 'pure', not both";
  EXPECT_TRUE(ReportedError(r.diags, kMsg, 3, "A.1.10"));
  EXPECT_TRUE(ReportedError(r.diags, kMsg, 4, "A.1.10"));
  EXPECT_FALSE(ReportedError(r.diags, kMsg, 5, "A.1.10"));
  EXPECT_FALSE(ReportedError(r.diags, kMsg, 6, "A.1.10"));
  EXPECT_FALSE(
      ReportedError(r.diags, "is written before its 'extern'", 4, "A.1.10"));
}

TEST(ConstraintItemsParsing, NestedBracesInConstraintBlock) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c {\n"
      "    if (x > 0) {\n"
      "      if (x > 10) {\n"
      "        if (x > 100) {\n"
      "          x < 1000;\n"
      "        }\n"
      "      }\n"
      "    }\n"
      "  }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, DistItemValueRangeWithoutWeight) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist { 10, 20, [30:40] }; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[1]->name, "c");
}

TEST(ConstraintItemsParsing, ConstraintPrimaryImplicitHandle) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  constraint c { solve this.x before this.y; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[2]->name, "c");
}

TEST(ConstraintItemsParsing, ConstraintPrimaryClassScope) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { solve C::x before C::x; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[1]->name, "c");
}

// constraint_primary ::= ... hierarchical_identifier select [ ( ) ]: the
// empty parentheses an array built-in method takes, which A.10 footnote 12
// allows on no other primary; the elaborator holds that rule.
TEST(ConstraintItemsParsing, ConstraintPrimaryWithParens) {
  auto r = Parse(
      "class C;\n"
      "  rand int a [];\n"
      "  constraint c { disable soft a.size(); }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  const auto* member = r.cu->classes[0]->members[1];
  EXPECT_EQ(member->name, "c");
  ASSERT_EQ(member->constraint_items.size(), 1u);
  EXPECT_EQ(member->constraint_items[0]->kind,
            ConstraintItemKind::kDisableSoft);
}

// uniqueness_constraint ::= unique { range_list }: the brace list is a
// range_list, so a value_range element (here the range [1:5]) is admitted
// alongside a plain variable, not just the bare-identifier list.
TEST(ConstraintItemsParsing, UniquenessConstraintValueRange) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { unique { [1:5], x }; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[1]->name, "c");
}

// dist_item ::= value_range [ dist_weight ] | default :/ expression: the
// default alternative is grammatical only with the :/ weight operator, so the
// closest rejected input -- 'default' followed by the := operator -- is not
// derivable from this production and the parser reports it.
TEST(ConstraintItemsParsing, ErrorDistDefaultEqualWeight) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist { [0:9] :/ 1, default := 1 }; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a distribution's default specification takes its "
                            "weight through :/ and nothing else",
                            3, "18.5.3"));
}

constexpr const char* kItemsDoNotParse =
    "the constraint block's items do not parse from here";

// constraint_block ::= { { constraint_block_item } }: text from which A.1.10
// derives no item is reported where the block's parse breaks off, once per
// block (#7580).
TEST(ConstraintItemsParsing, ItemOutsideTheGrammarIsError) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  constraint c1 { x > ; }\n"
      "  constraint c2 { if x > 0 y < 4; }\n"
      "  constraint c3 { x dist ; }\n"
      "  constraint c4 { solve x y; }\n"
      "  constraint c5 { x < y; y < 9; }\n"
      "  constraint c6 { foreach ([i]) x > 0; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags, kItemsDoNotParse, 3, "A.1.10"));
  EXPECT_TRUE(ReportedError(r.diags, kItemsDoNotParse, 4, "A.1.10"));
  EXPECT_TRUE(ReportedError(r.diags, kItemsDoNotParse, 5, "A.1.10"));
  EXPECT_TRUE(ReportedError(r.diags, kItemsDoNotParse, 6, "A.1.10"));
  EXPECT_FALSE(ReportedError(r.diags, kItemsDoNotParse, 7, "A.1.10"));
  EXPECT_TRUE(ReportedError(r.diags, kItemsDoNotParse, 8, "A.1.10"));
}

// An out-of-block constraint's block and the inline block of a
// randomize() with are read by the same parse (#7580).
TEST(ConstraintItemsParsing, OutOfBlockAndInlineItemOutsideTheGrammarIsError) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint e;\n"
      "endclass\n"
      "constraint C::e { x < ; }\n"
      "module m;\n"
      "  C obj;\n"
      "  initial void'(obj.randomize() with { x dist ; });\n"
      "  initial void'(obj.randomize() with { x < 4; });\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, kItemsDoNotParse, 5, "A.1.10"));
  EXPECT_TRUE(ReportedError(r.diags, kItemsDoNotParse, 8, "A.1.10"));
  EXPECT_FALSE(ReportedError(r.diags, kItemsDoNotParse, 9, "A.1.10"));
}

// constraint_set ::= constraint_expression | { { constraint_expression } }:
// a solve-before is an item of the block alone, never one of a set (#7580).
TEST(ConstraintItemsParsing, SolveBeforeInAConstraintSetIsError) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  constraint c1 { if (x > 0) { solve x before y; } }\n"
      "  constraint c2 { x > 0 -> solve x before y; }\n"
      "  constraint c3 { solve x before y; if (x > 0) y < 3; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags, kItemsDoNotParse, 3, "A.1.10"));
  EXPECT_TRUE(ReportedError(r.diags, kItemsDoNotParse, 4, "A.1.10"));
  EXPECT_FALSE(ReportedError(r.diags, kItemsDoNotParse, 5, "A.1.10"));
}

// A constraint_set written in braces ends its item at the '}', so a ';' after
// it stands where no item A.1.10 writes begins (#7580).
TEST(ConstraintItemsParsing, SemicolonAfterAConstraintSetIsError) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b;\n"
      "  constraint c1 { a > 5 -> { b < 10; }; }\n"
      "  constraint c2 { a > 5 -> { b < 10; } }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags, kItemsDoNotParse, 3, "A.1.10"));
  EXPECT_FALSE(ReportedError(r.diags, kItemsDoNotParse, 4, "A.1.10"));
}

// ps_or_hierarchical_array_identifier opens with an implicit_class_handle,
// super as well as this, so a foreach over a base class's array parses
// (#7580).
TEST(ConstraintItemsParsing, ForeachOverASuperArrayParses) {
  auto r = Parse(
      "class B;\n"
      "  rand int arr [4];\n"
      "endclass\n"
      "class C extends B;\n"
      "  constraint c { foreach (super.arr[i]) super.arr[i] < 4; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  const auto* member = r.cu->classes[1]->members[0];
  ASSERT_TRUE(member->constraint_items_parsed);
  ASSERT_EQ(member->constraint_items.size(), 1u);
  EXPECT_EQ(member->constraint_items[0]->kind, ConstraintItemKind::kForeach);
}

}  // namespace
