#include <gtest/gtest.h>

#include "fixture_parser.h"

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

}  // namespace
