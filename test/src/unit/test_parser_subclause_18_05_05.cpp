#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

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

std::string ImplicationItem(const std::string& item) {
  return "class C;\n"
         "  rand bit [3:0] a;\n"
         "  rand bit [3:0] b;\n"
         "  constraint k { " +
         item +
         " }\n"
         "endclass\n";
}

const char* const kNoParse =
    "the constraint block's items do not parse from here";

TEST(ConstraintImplicationParsing, AnOutOfBlockImplicationIsAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] a;\n"
      "  rand bit [3:0] b;\n"
      "  constraint k;\n"
      "endclass\n"
      "constraint C::k { (a == 0) -> b == 1; a > 2 -> { b == 1; } }\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintImplicationParsing, AnEmptyBracedSetIsAccepted) {
  EXPECT_FALSE(Parse(ImplicationItem("(a == 0) -> {}")).has_errors);
}

TEST(ConstraintImplicationParsing, NoConsequentIsRejected) {
  auto r = Parse(ImplicationItem("(a == 0) -> ;"));
  EXPECT_TRUE(ReportedError(r.diags, kNoParse, 4, "A.1.10"));
}

TEST(ConstraintImplicationParsing, TheConsequentsSemicolonLeftOffIsRejected) {
  auto r = Parse(ImplicationItem("(a == 0) -> b == 1"));
  EXPECT_TRUE(ReportedError(r.diags, kNoParse, 4, "A.1.10"));
}

}  // namespace
