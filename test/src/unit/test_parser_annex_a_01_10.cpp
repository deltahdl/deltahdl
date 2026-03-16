#include "fixture_parser.h"

using namespace delta;

namespace {

// === Existing tests ===

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

TEST(ConstraintItemsParsing, ForeachConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int arr[10];\n"
      "  constraint c {\n"
      "    foreach (arr[i]) arr[i] inside {[0:255]};\n"
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

TEST(ConstraintItemsParsing, UniquenessConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, c;\n"
      "  constraint c_uniq { unique {a, b, c}; }\n"
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

TEST(ConstraintItemsParsing, ConstraintPrototype) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c_x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, ExternConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint c_x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, StaticConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  static constraint c_x { x > 0; }\n"
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

// --- Moved from test_parser_clause_18_05.cpp ---

TEST(ConstraintItemsParsing, ClassWithTwoExprConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c1 { x > 0; x < 100; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
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

// --- Moved from test_parser_clause_18_05_01.cpp ---

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

TEST(ConstraintItemsParsing, ExternConstraintDeclaration) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint c;\n"
      "endclass\n"
      "constraint C::c { x > 0; }\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, ImplicitConstraintPrototype) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c;\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
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

TEST(ConstraintItemsParsing, ExternConstraintPrototypeVerifiesAst) {
  auto r = Parse(
      "class A;\n"
      "  rand int x;\n"
      "  extern constraint c1;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  bool found = false;
  for (auto* m : r.cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kConstraint && m->name == "c1") {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// --- Moved from test_parser_clause_18_05_02.cpp ---

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
  EXPECT_EQ(members[2]->name, "c2");
  EXPECT_EQ(members[3]->name, "c3");
  EXPECT_EQ(members[4]->name, "c4");
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
  EXPECT_EQ(members[2]->name, "c2");
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

// --- Moved from test_parser_clause_18_05_03.cpp ---

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

TEST(ConstraintItemsParsing, DistDivideWeightMultipleValues) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {1 :/ 1, 2 :/ 1, 3 :/ 1, 4 :/ 1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, DistWithRangeAndEqualWeight) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[0:3] := 1, [4:7] := 2}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, DistWithMixedWeightTypes) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {0 := 1, [1:10] :/ 5, 11 := 3}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, DistWithDefaultWeight) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[0:255] :/ 1, default :/ 1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, DistWithExpressionWeights) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {1 := 2 * 3, 2 := 4 + 1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, DistWithNegativeValues) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {-10 := 1, 0 := 2, 10 := 1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, DistMultipleConstraints) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  constraint cx { x dist {[0:100] := 1}; }\n"
      "  constraint cy { y dist {[0:50] :/ 2, [51:100] :/ 1}; }\n"
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

// --- Moved from test_parser_clause_18_05_04.cpp ---

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

// --- Moved from test_parser_clause_18_05_06.cpp ---

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

// --- Moved from test_parser_clause_18_05_07_01.cpp ---

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

// --- Moved from test_parser_clause_18_05_10.cpp ---

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

// --- Moved from test_parser_clause_18_05_13_02.cpp ---

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

// === Step 9: Missing tests ===

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
}

TEST(ConstraintItemsParsing, ExternConstraintDeclExtendsOverride) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint c;\n"
      "endclass\n"
      "constraint :extends C::c { x > 0; }\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstraintItemsParsing, ExternConstraintDeclFinalOverride) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint c;\n"
      "endclass\n"
      "constraint :initial :final C::c { x > 0; }\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
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

// === Error conditions ===

TEST(ConstraintItemsParsing, ErrorConstraintMissingName) {
  auto r = Parse(
      "class C;\n"
      "  constraint { x > 0; }\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConstraintItemsParsing, ErrorConstraintPrototypeMissingSemicolon) {
  auto r = Parse(
      "class C;\n"
      "  constraint c\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConstraintItemsParsing, ErrorExternConstraintMissingScope) {
  auto r = Parse(
      "constraint c { x > 0; }\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConstraintItemsParsing, ErrorConstraintUnmatchedBrace) {
  auto r = Parse(
      "class C;\n"
      "  constraint c { x > 0;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConstraintItemsParsing, ErrorExternConstraintMissingIdentifier) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint c;\n"
      "endclass\n"
      "constraint C:: { x > 0; }\n");
  EXPECT_TRUE(r.has_errors);
}

// === Edge cases ===

TEST(ConstraintItemsParsing, ConstraintOnlyFinalOverride) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint :final c { x > 0; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[1]->name, "c");
}

TEST(ConstraintItemsParsing, ConstraintOnlyExtendsOverride) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint :extends c { x > 0; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[1]->name, "c");
}

TEST(ConstraintItemsParsing, ConstraintExtendsAndFinalOverride) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint :extends :final c { x > 0; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[1]->name, "c");
}

TEST(ConstraintItemsParsing, MultipleConstraintBlockItems) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, c, d;\n"
      "  constraint all {\n"
      "    a > 0;\n"
      "    soft b == 1;\n"
      "    a > 5 -> { b < 10; c > 0; };\n"
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

TEST(ConstraintItemsParsing, StaticExternConstraintPrototype) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  static extern constraint c;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[1]->name, "c");
  EXPECT_TRUE(r.cu->classes[0]->members[1]->is_static);
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

}  // namespace
