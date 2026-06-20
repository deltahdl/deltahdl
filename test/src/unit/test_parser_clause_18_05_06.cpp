#include "fixture_parser.h"

using namespace delta;

namespace {

// 18.5.6: constraint_expression includes the if-else form
// "if ( expression ) constraint_set [ else constraint_set ]". A
// single-statement then-branch with an else branch parses as a valid constraint
// expression inside a constraint block.
TEST(ConstraintIfElseParsing, IfElseFormAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] mode;\n"
      "  rand bit [7:0] len;\n"
      "  constraint c { if (mode == 1) len < 10; else len > 100; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.6: the then- and else-branches may each be an unnamed constraint set,
// i.e. a brace-enclosed group of constraint expressions.
TEST(ConstraintIfElseParsing, BracedConstraintSetsAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] mode;\n"
      "  rand bit [7:0] len;\n"
      "  rand bit [7:0] size;\n"
      "  constraint k { if (mode == 1) { len < 10; size > 2; }\n"
      "                 else { len > 100; size < 8; } }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.6: the else constraint_set is optional. An if constraint with no else
// branch is a valid constraint expression on its own.
TEST(ConstraintIfElseParsing, IfWithoutElseAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] mode;\n"
      "  rand bit [7:0] len;\n"
      "  constraint c { if (mode == 1) len < 10; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.6: chaining "else if" yields a cascade of if-else constraints, where the
// else branch is itself another if. This chained form parses without error.
TEST(ConstraintIfElseParsing, ElseIfChainAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] mode;\n"
      "  rand bit [7:0] len;\n"
      "  constraint c { if (mode == 1) len < 10;\n"
      "                 else if (mode == 2) len > 100; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.6: an else may be omitted from a nested if sequence; the dangling else
// associates with the closest preceding if that lacks one. The nested form is
// accepted as a valid constraint expression.
TEST(ConstraintIfElseParsing, DanglingElseNestedFormAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] mode;\n"
      "  rand bit [7:0] len;\n"
      "  constraint d { if (mode != 2) if (mode == 1) len < 10;"
      " else len > 100; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
