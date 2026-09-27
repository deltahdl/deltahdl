#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

namespace {

TEST(ConfigPositionalParamNotation, SinglePositionalRejected) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(8);\n"
      "endconfig\n");
  // Only named notation is permitted, so the parser demands the '.' that opens
  // a named_parameter_assignment where the positional value stands.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '.', got integer literal", 3, "33.4.3"));
}

TEST(ConfigPositionalParamNotation, MultiplePositionalRejected) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(8, 16);\n"
      "endconfig\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '.', got integer literal", 3, "33.4.3"));
}

TEST(ConfigPositionalParamNotation, MixedNamedThenPositionalRejected) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(8), 16);\n"
      "endconfig\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '.', got integer literal", 3, "33.4.3"));
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

// Syntax 33-4 opens a config with `{ local_parameter_declaration ; }`, and
// A.2.1.1 lets that declaration name a data type before its assignments.
TEST(ConfigLocalparam, DataTypedLocalparamParses) {
  auto r = Parse(
      "config c;\n"
      "  localparam int S = 24;\n"
      "  design work.top;\n"
      "  instance top.a1 use #(.W(S));\n"
      "endconfig\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  ASSERT_EQ(r.cu->configs[0]->local_params.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->local_params[0].first, "S");
}

// The same declaration's list_of_param_assignments declares each name it lists.
TEST(ConfigLocalparam, LocalparamListDeclaresEachName) {
  auto r = Parse(
      "config c;\n"
      "  localparam S = 24, T = 3;\n"
      "  design work.top;\n"
      "endconfig\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  const auto& params = r.cu->configs[0]->local_params;
  ASSERT_EQ(params.size(), 2u);
  EXPECT_EQ(params[0].first, "S");
  EXPECT_EQ(params[1].first, "T");
}

}  // namespace
