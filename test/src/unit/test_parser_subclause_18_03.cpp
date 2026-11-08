#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConstraintFourState, TripleEqualOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x === 0; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "4-state equality operator is not allowed in a constraint", 3,
      "18.3"));
}

TEST(ConstraintFourState, TripleNotEqualOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x !== 0; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "4-state equality operator is not allowed in a constraint", 3,
      "18.3"));
}

TEST(ConstraintFourState, FourStateLiteralRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x == 4'b01xz; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "4-state value is not allowed in a constraint", 3, "18.3"));
}

TEST(ConstraintFourState, QuestionMarkDigitRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "  constraint c { x == 4'b10??; }\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "4-state value is not allowed in a constraint", 3, "18.3"));
}

TEST(ConstraintFourState, TwoStateConstraintAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x == 5; x inside {1, 2, 3}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
