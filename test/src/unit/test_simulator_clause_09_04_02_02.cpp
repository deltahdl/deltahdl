// §9.4.2.2: Implicit event_expression list

#include <gtest/gtest.h>

#include "helpers_sensitivity.h"

namespace {

TEST(TimingControl, ImplicitSensitivityIncludesRHS) {
  std::vector<VarRef> refs = {
      {"a", ExprRole::kRHS},
      {"b", ExprRole::kPureLHS},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "a");
}

TEST(TimingControl, ImplicitSensitivityIncludesSubroutineArgs) {
  std::vector<VarRef> refs = {
      {"f_arg", ExprRole::kSubroutineArg},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "f_arg");
}

TEST(TimingControl, ImplicitSensitivityIncludesCaseExpr) {
  std::vector<VarRef> refs = {
      {"sel", ExprRole::kCaseExpr},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "sel");
}

TEST(TimingControl, ImplicitSensitivityIncludesConditionalExpr) {
  std::vector<VarRef> refs = {
      {"cond", ExprRole::kConditionalExpr},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "cond");
}

TEST(TimingControl, ImplicitSensitivityIncludesLHSIndex) {
  std::vector<VarRef> refs = {
      {"idx", ExprRole::kLHSIndex},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "idx");
}

TEST(TimingControl, ImplicitSensitivityExcludesTimingControl) {
  std::vector<VarRef> refs = {
      {"a", ExprRole::kRHS},
      {"clk", ExprRole::kTimingControl},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "a");
}

TEST(TimingControl, ImplicitSensitivityExcludesPureLHS) {
  std::vector<VarRef> refs = {
      {"out", ExprRole::kPureLHS},
      {"in", ExprRole::kRHS},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "in");
}

TEST(TimingControl, ImplicitSensitivityMixedRoles) {
  std::vector<VarRef> refs = {
      {"a", ExprRole::kRHS},      {"b", ExprRole::kSubroutineArg},
      {"c", ExprRole::kPureLHS},  {"d", ExprRole::kTimingControl},
      {"e", ExprRole::kLHSIndex},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 3u);  // a, b, e
}

}  // namespace
