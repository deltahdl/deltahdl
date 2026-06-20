#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// 18.3: 4-state operators (===, !==) are illegal in a constraint and shall
// result in an error.
TEST(ConstraintFourState, TripleEqualOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x === 0; }\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConstraintFourState, TripleNotEqualOperatorRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x !== 0; }\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// 18.3: 4-state values (x or z) are illegal in a constraint.
TEST(ConstraintFourState, FourStateLiteralRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x == 4'b01xz; }\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// A constraint that uses only 2-state values and 2-state operators is legal.
TEST(ConstraintFourState, TwoStateConstraintAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x == 5; x inside {1, 2, 3}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
