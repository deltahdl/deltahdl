#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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
  EXPECT_TRUE(r.has_errors);
}

TEST(ConstraintSideEffect, DecrementOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x == y--; }\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// 18.5: the side-effect prohibition applies to the prefix position of the
// increment operator as well as the postfix position exercised above.
TEST(ConstraintSideEffect, PrefixIncrementOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { ++x < 10; }\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// 18.5: likewise the prefix position of the decrement operator is rejected.
TEST(ConstraintSideEffect, PrefixDecrementOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { --x < 10; }\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
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
  EXPECT_TRUE(r.has_errors);
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
  EXPECT_TRUE(r.has_errors);
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
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
