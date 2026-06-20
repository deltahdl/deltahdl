#include <gtest/gtest.h>

#include "helpers_sensitivity.h"

namespace {

TEST(ImplicitSensitivity, ImplicitSensitivityIncludesRHS) {
  std::vector<VarRef> refs = {
      {"a", ExprRole::kRHS},
      {"b", ExprRole::kPureLHS},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "a");
}

TEST(ImplicitSensitivity, ImplicitSensitivityIncludesSubroutineArgs) {
  std::vector<VarRef> refs = {
      {"f_arg", ExprRole::kSubroutineArg},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "f_arg");
}

TEST(ImplicitSensitivity, ImplicitSensitivityIncludesCaseExpr) {
  std::vector<VarRef> refs = {
      {"sel", ExprRole::kCaseExpr},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "sel");
}

TEST(ImplicitSensitivity, ImplicitSensitivityIncludesConditionalExpr) {
  std::vector<VarRef> refs = {
      {"cond", ExprRole::kConditionalExpr},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "cond");
}

TEST(ImplicitSensitivity, ImplicitSensitivityIncludesLHSIndex) {
  std::vector<VarRef> refs = {
      {"idx", ExprRole::kLHSIndex},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "idx");
}

TEST(ImplicitSensitivity, ImplicitSensitivityExcludesPureLHS) {
  std::vector<VarRef> refs = {
      {"out", ExprRole::kPureLHS},
      {"in", ExprRole::kRHS},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "in");
}

TEST(ImplicitSensitivity, ImplicitSensitivityExcludesTimingControl) {
  std::vector<VarRef> refs = {
      {"a", ExprRole::kRHS},
      {"clk", ExprRole::kTimingControl},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "a");
}

TEST(ImplicitSensitivity, EmptyRefsProduceEmptyList) {
  std::vector<VarRef> refs = {};
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 0u);
}

}  // namespace
