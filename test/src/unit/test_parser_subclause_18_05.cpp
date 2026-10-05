#include <gtest/gtest.h>

#include <string_view>
#include <vector>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_class.h"

using namespace delta;

namespace {

// 18.5: operators with side effects, such as ++ and --, are not allowed in a
// constraint expression.
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

// 18.5: the side-effect prohibition applies to the prefix position of the
// increment operator as well as the postfix position exercised above.
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

// 18.5: likewise the prefix position of the decrement operator is rejected.
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

// A constraint without side-effecting operators parses cleanly.
TEST(ConstraintSideEffect, PlainArithmeticAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand int y;\n"
      "  constraint c { x == y + 1; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5: dist expressions may not appear in other expressions. A bare
// "expression dist { dist_list }" that terminates the constraint relation is
// the accepting form.
TEST(ConstraintDistNesting, TopLevelDistAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {1:=1, 2:=3}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5: a dist expression is a complete expression_or_dist, so it remains
// legal as the whole relation of a constraint nested inside an if branch —
// the restriction bars operand use, not a legal nested position.
TEST(ConstraintDistNesting, DistInIfBranchAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand bit a;\n"
      "  constraint c { if (a) x dist {1:=1, 2:=3}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5: using a dist expression as the operand of a surrounding expression
// (here, parenthesized inside an equality) is rejected.
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

// 18.5: a dist expression may not be combined with another operator; an
// arithmetic continuation after the dist_list is rejected.
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

// 18.5: a dist expression may not form the antecedent of an implication; the
// left side of '->' must be a plain expression, so a dist there is rejected.
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

// §18.5 names every constraint block: Syntax 18-1 writes the declaration as
// `constraint constraint_identifier constraint_block`. A block whose name is
// missing is rejected at the '{' that stands where the name belongs, and the
// report names §18.5 rather than the token it wanted. The case at the head of
// this file rejects a source by the rule §18.5 states about dist expressions;
// this one is rejected by the same subclause's syntax, so the file holds both
// a rule-level rejection and a token-level one naming §18.5.
TEST(ConstraintBlock, MalformedConstraintNames18_5) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint { x > 0; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier", 3, "18.5"));
}

// The first constraint block of the class `r` parsed, null where it declares
// none.
const ClassMember* BlockOf(const ParseResult& r) {
  if (r.cu == nullptr || r.cu->classes.empty()) return nullptr;
  for (const ClassMember* m : r.cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kConstraint) return m;
  }
  return nullptr;
}

// The kind of each of `items`, in order.
std::vector<ConstraintItemKind> KindsOf(
    const std::vector<ConstraintItem*>& items) {
  std::vector<ConstraintItemKind> kinds;
  kinds.reserve(items.size());
  for (const ConstraintItem* item : items) kinds.push_back(item->kind);
  return kinds;
}

// §18.5 (A.1.10): a constraint block keeps its items in the order the source
// wrote them, whatever their kinds, so it can be written back as it was
// (#5040).
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

// §18.5.9: a solve-before keeps both of its lists.
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

// §18.5.5: an implication keeps the constraint set it governs, a soft item
// among it.
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

// §18.5.6: an if-else keeps both its sets, an else binding to the closest if.
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

// §18.5.7.1: a foreach keeps its loop variables, a skipped one in its place.
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
