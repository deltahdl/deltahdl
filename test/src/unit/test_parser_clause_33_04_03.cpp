#include "fixture_parser.h"

namespace {

TEST(ConfigPositionalParamNotation, SinglePositionalRejected) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(8);\n"
      "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConfigPositionalParamNotation, MultiplePositionalRejected) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(8, 16);\n"
      "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConfigPositionalParamNotation, MixedNamedThenPositionalRejected) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(8), 16);\n"
      "endconfig\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ConfigPositionalParamNotation, NamedAssignmentAccepted) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(8));\n"
      "endconfig\n");
  EXPECT_FALSE(r.has_errors);
}

// A named override with empty parentheses resets that single parameter to its
// module default (§33.4.3); it must parse as a valid override.
TEST(ConfigEmptyParamOverride, EmptyParamExprAccepted) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W());\n"
      "endconfig\n");
  EXPECT_FALSE(r.has_errors);
}

// A subset of named overrides may be left empty while others carry values.
TEST(ConfigEmptyParamOverride, MixedEmptyAndValuedAccepted) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(), .D(512));\n"
      "endconfig\n");
  EXPECT_FALSE(r.has_errors);
}

// An empty override list resets every parameter of the cell to its module
// default (§33.4.3); the empty list must parse as a valid use clause.
TEST(ConfigEmptyParamOverride, EmptyParamListAccepted) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #();\n"
      "endconfig\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
