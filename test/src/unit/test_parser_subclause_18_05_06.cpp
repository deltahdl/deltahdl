#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConstraintIfElseParsing, IfElseFormAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] mode;\n"
      "  rand bit [7:0] len;\n"
      "  constraint c { if (mode == 1) len < 10; else len > 100; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

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

TEST(ConstraintIfElseParsing, IfWithoutElseAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] mode;\n"
      "  rand bit [7:0] len;\n"
      "  constraint c { if (mode == 1) len < 10; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
}

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

ParseResult ParseIfElseConstraint(const std::string& body) {
  return Parse(
      "class C;\n"
      "  rand bit [3:0] p, q;\n"
      "  constraint ie { " +
      body +
      " }\n"
      "endclass\n");
}

TEST(ConstraintIfElseParsing, AnOutOfBlockIfElseIsAccepted) {
  auto r = Parse(
      "class C;\n"
      "  rand bit [3:0] p, q;\n"
      "  constraint ie;\n"
      "endclass\n"
      "constraint C::ie { if (p > 3) q == 1; else { q == 2; } }\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintIfElseParsing, EmptyBracedSetsAreAccepted) {
  EXPECT_FALSE(ParseIfElseConstraint("if (p > 3) {} else {}").has_errors);
}

TEST(ConstraintIfElseParsing, AConditionWithoutParenthesesIsRejected) {
  auto r = ParseIfElseConstraint("if p q == 1;");
  EXPECT_TRUE(ReportedError(
      r.diags, "the constraint block's items do not parse from here", 3,
      "A.1.10"));
}

TEST(ConstraintIfElseParsing, AnEmptyThenSetIsRejected) {
  auto r = ParseIfElseConstraint("if (p > 3) ;");
  EXPECT_TRUE(ReportedError(
      r.diags, "the constraint block's items do not parse from here", 3,
      "A.1.10"));
}

TEST(ConstraintIfElseParsing, AnEmptyElseSetIsRejected) {
  auto r = ParseIfElseConstraint("if (p > 3) q == 1; else ;");
  EXPECT_TRUE(ReportedError(
      r.diags, "the constraint block's items do not parse from here", 3,
      "A.1.10"));
}

}  // namespace
