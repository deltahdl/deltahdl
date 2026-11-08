#include <gtest/gtest.h>

#include <string_view>
#include <vector>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_class.h"

using namespace delta;

namespace {

TEST(ConstraintSideEffect, IncrementOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x == y++; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "operator with side effects is not allowed in a constraint", 3,
      "18.5"));
}

TEST(ConstraintSideEffect, DecrementOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x == y--; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "operator with side effects is not allowed in a constraint", 3,
      "18.5"));
}

TEST(ConstraintSideEffect, PrefixIncrementOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { ++x < 10; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "operator with side effects is not allowed in a constraint", 3,
      "18.5"));
}

TEST(ConstraintSideEffect, PrefixDecrementOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { --x < 10; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "operator with side effects is not allowed in a constraint", 3,
      "18.5"));
}

TEST(ConstraintSideEffect, PlainArithmeticAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint c { x == y + 1; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintDistNesting, TopLevelDistAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {1:=1, 2:=3}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintDistNesting, DistInIfBranchAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand bit a;\n"
      "  constraint c { if (a) x dist {1:=1, 2:=3}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintDistNesting, DistInsideParenthesizedOperandRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint c { y == (x dist {1:=1, 2:=3}); }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a dist expression may not appear within another expression", 4,
      "18.5"));
}

TEST(ConstraintDistNesting, DistFollowedByOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint c { x dist {1:=1} + y; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a dist expression may not appear within another expression", 4,
      "18.5"));
}

TEST(ConstraintDistNesting, DistAsImplicationAntecedentRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint c { x dist {1:=1} -> y > 0; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a dist expression may not appear within another expression", 4,
      "18.5"));
}

TEST(ConstraintBlock, MalformedConstraintNames18_5) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint { x > 0; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier", 3, "18.5"));
}

const ClassMember* BlockOf(const ParseResult& r) {
  if (r.cu == nullptr || r.cu->classes.empty()) return nullptr;
  for (const ClassMember* m : r.cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kConstraint) return m;
  }
  return nullptr;
}

std::vector<ConstraintItemKind> KindsOf(
    const std::vector<ConstraintItem*>& items) {
  std::vector<ConstraintItemKind> kinds;
  kinds.reserve(items.size());
  for (const ConstraintItem* item : items) kinds.push_back(item->kind);
  return kinds;
}

TEST(ConstraintItems, ABlockKeepsItsItemsInSourceOrder) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, x;\n"
      "  constraint c { solve a before b; x dist {1 := 2, [3:4] :/ 1};\n"
      "                 unique {a, b}; a < b; soft x > 1; disable soft x; }\n"
      "endclass\n");
  const ClassMember* block = BlockOf(r);
  ASSERT_NE(block, nullptr);
  ASSERT_TRUE(block->constraint_items_parsed);
  EXPECT_EQ(
      KindsOf(block->constraint_items),
      (std::vector<ConstraintItemKind>{
          ConstraintItemKind::kSolveBefore, ConstraintItemKind::kExpression,
          ConstraintItemKind::kUnique, ConstraintItemKind::kExpression,
          ConstraintItemKind::kExpression, ConstraintItemKind::kDisableSoft}));
  EXPECT_EQ(block->constraint_items[1]->dist.size(), 2U);
  EXPECT_EQ(block->constraint_items[2]->exprs.size(), 2U);
  EXPECT_TRUE(block->constraint_items[4]->soft);
}

TEST(ConstraintItems, ASolveBeforeKeepsBothLists) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, x;\n"
      "  constraint c { solve a, b before x; }\n"
      "endclass\n");
  const ClassMember* block = BlockOf(r);
  ASSERT_NE(block, nullptr);
  ASSERT_EQ(block->constraint_items.size(), 1U);
  EXPECT_EQ(block->constraint_items[0]->exprs.size(), 2U);
  EXPECT_EQ(block->constraint_items[0]->after.size(), 1U);
}

TEST(ConstraintItems, AnImplicationKeepsTheSetItGoverns) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, x;\n"
      "  constraint c { a > 0 -> { b == 1; soft x == 2; } }\n"
      "endclass\n");
  const ClassMember* block = BlockOf(r);
  ASSERT_NE(block, nullptr);
  ASSERT_EQ(block->constraint_items.size(), 1U);
  const ConstraintItem* item = block->constraint_items[0];
  EXPECT_EQ(item->kind, ConstraintItemKind::kImplication);
  ASSERT_EQ(item->body.size(), 2U);
  EXPECT_TRUE(item->body[1]->soft);
}

TEST(ConstraintItems, AnElseBindsToTheClosestIf) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, x;\n"
      "  constraint c { if (a) if (b) x == 1; else { x == 2; x < 3; } }\n"
      "endclass\n");
  const ClassMember* block = BlockOf(r);
  ASSERT_NE(block, nullptr);
  ASSERT_EQ(block->constraint_items.size(), 1U);
  const ConstraintItem* outer = block->constraint_items[0];
  EXPECT_FALSE(outer->has_else);
  ASSERT_EQ(outer->body.size(), 1U);
  const ConstraintItem* inner = outer->body[0];
  EXPECT_EQ(inner->kind, ConstraintItemKind::kIfElse);
  EXPECT_TRUE(inner->has_else);
  EXPECT_EQ(inner->else_body.size(), 2U);
}

TEST(ConstraintItems, AForeachKeepsItsLoopVariables) {
  auto r = Parse(
      "class C;\n"
      "  rand int m[2][3][4];\n"
      "  constraint c { foreach (m[i, , k]) m[i][0][k] < 4; }\n"
      "endclass\n");
  const ClassMember* block = BlockOf(r);
  ASSERT_NE(block, nullptr);
  ASSERT_EQ(block->constraint_items.size(), 1U);
  const ConstraintItem* item = block->constraint_items[0];
  EXPECT_EQ(item->kind, ConstraintItemKind::kForeach);
  EXPECT_EQ(item->loop_vars, (std::vector<std::string_view>{"i", "", "k"}));
  EXPECT_EQ(item->body.size(), 1U);
}

}  // namespace
