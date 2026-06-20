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

}  // namespace
