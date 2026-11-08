#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ConstraintImplicationParsing, SingleStatementConsequentAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] a;\n"
      "  rand bit [3:0] b;\n"
      "  constraint c { (a == 0) -> b == 1; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

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
