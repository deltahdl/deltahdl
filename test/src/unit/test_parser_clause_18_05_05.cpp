#include "fixture_parser.h"

using namespace delta;

namespace {

// 18.5.5: constraint_expression includes the implication form
// "expression -> constraint_set". A single-statement consequent parses as a
// valid constraint expression inside a constraint block.
TEST(ConstraintImplicationParsing, SingleStatementConsequentAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] a;\n"
      "  rand bit [3:0] b;\n"
      "  constraint c { (a == 0) -> b == 1; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.5: the constraint_set on the right of "->" may be an unnamed constraint
// set, i.e. a brace-enclosed group of constraint expressions.
TEST(ConstraintImplicationParsing, BracedConstraintSetConsequentAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] a;\n"
      "  rand bit [3:0] b;\n"
      "  rand bit [3:0] c;\n"
      "  constraint k { (a == 0) -> { b == 1; c == 2; } }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

// 18.5.5: the antecedent expression may be any integral or real expression. A
// real-typed antecedent (a comparison of a rand real member) is a valid
// implication antecedent and parses without error.
TEST(ConstraintImplicationParsing, RealTypedAntecedentAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand real r;\n"
      "  rand bit [3:0] b;\n"
      "  constraint c { (r < 1.5) -> b == 1; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
