#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

namespace {

bool PositionalOverrideRuleRejected(const char* rule, uint32_t line) {
  auto r = Parse(std::string("config c;\n"
                             "  design top;\n") +
                 rule + "endconfig\n");
  return ReportedError(r.diags, "expected '.', got integer literal", line,
                       "33.4.3");
}

TEST(ConfigPositionalParamNotation, SinglePositionalRejected) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(8);\n"
      "endconfig\n");
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

TEST(ConfigPositionalParamNotation, PositionalUnderACellClauseUseRejected) {
  EXPECT_TRUE(PositionalOverrideRuleRejected("  cell lib.m use #(8);\n", 3));
}

TEST(ConfigPositionalParamNotation, PositionalAfterAUseCellRejected) {
  EXPECT_TRUE(
      PositionalOverrideRuleRejected("  instance top.a1 use lib.m #(8);\n", 3));
}

TEST(ConfigPositionalParamNotation, PositionalThenNamedRejected) {
  EXPECT_TRUE(PositionalOverrideRuleRejected(
      "  instance top.a1 use #(8, .W(16));\n", 3));
}

TEST(ConfigPositionalParamNotation, NamedAfterAUseCellAccepted) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  cell lib.m use lib.m #(.W(8));\n"
      "endconfig\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConfigLocalparam, DISABLED_LocalparamWithoutAValueRejected) {
  auto r = Parse(
      "config c;\n"
      "  localparam X;\n"
      "  design top;\n"
      "endconfig\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "parameter declaration requires a default value", 2, "33.4.3"));
}

TEST(ConfigEmptyParamOverride, EmptyParamExprAccepted) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W());\n"
      "endconfig\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConfigEmptyParamOverride, MixedEmptyAndValuedAccepted) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #(.W(), .D(512));\n"
      "endconfig\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(ConfigEmptyParamOverride, EmptyParamListAccepted) {
  auto r = Parse(
      "config c;\n"
      "  design top;\n"
      "  instance top.a1 use #();\n"
      "endconfig\n");
  EXPECT_FALSE(r.has_errors);
}

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
  EXPECT_EQ(r.cu->configs[0]->local_params[0].name, "S");
}

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
  EXPECT_EQ(params[0].name, "S");
  EXPECT_EQ(params[1].name, "T");
}

}  // namespace
