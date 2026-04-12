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

TEST(ImplicitSensitivity, ImplicitSensitivityExcludesTimingControl) {
  std::vector<VarRef> refs = {
      {"a", ExprRole::kRHS},
      {"clk", ExprRole::kTimingControl},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "a");
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

TEST(ImplicitSensitivity, ImplicitSensitivityMixedRoles) {
  std::vector<VarRef> refs = {
      {"a", ExprRole::kRHS},      {"b", ExprRole::kSubroutineArg},
      {"c", ExprRole::kPureLHS},  {"d", ExprRole::kTimingControl},
      {"e", ExprRole::kLHSIndex},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 3u);
}

TEST(ImplicitSensitivity, AllExcludedRolesProduceEmptyList) {
  std::vector<VarRef> refs = {
      {"out", ExprRole::kPureLHS},
      {"clk", ExprRole::kTimingControl},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 0u);
}

TEST(ImplicitSensitivity, AllIncludedRolesProduceFullList) {
  std::vector<VarRef> refs = {
      {"a", ExprRole::kRHS},
      {"b", ExprRole::kSubroutineArg},
      {"c", ExprRole::kCaseExpr},
      {"d", ExprRole::kConditionalExpr},
      {"e", ExprRole::kLHSIndex},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 5u);
}

TEST(ImplicitSensitivity, EmptyRefsProduceEmptyList) {
  std::vector<VarRef> refs = {};
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 0u);
}

TEST(ImplicitSensitivity, SingleRhsOnly) {
  std::vector<VarRef> refs = {
      {"x", ExprRole::kRHS},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "x");
}

TEST(ImplicitSensitivity, PureLhsOnlyProducesEmpty) {
  std::vector<VarRef> refs = {
      {"out", ExprRole::kPureLHS},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 0u);
}

TEST(ImplicitSensitivity, TimingControlOnlyProducesEmpty) {
  std::vector<VarRef> refs = {
      {"clk", ExprRole::kTimingControl},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 0u);
}

TEST(ImplicitSensitivity, MultipleTimingControlsAllExcluded) {
  std::vector<VarRef> refs = {
      {"clk", ExprRole::kTimingControl},
      {"rst", ExprRole::kTimingControl},
      {"a", ExprRole::kRHS},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "a");
}

TEST(ImplicitSensitivity, MultiplePureLhsAllExcluded) {
  std::vector<VarRef> refs = {
      {"out1", ExprRole::kPureLHS},
      {"out2", ExprRole::kPureLHS},
      {"in", ExprRole::kRHS},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "in");
}

TEST(ImplicitSensitivity, CaseExprWithPureLhs) {
  std::vector<VarRef> refs = {
      {"sel", ExprRole::kCaseExpr},
      {"out", ExprRole::kPureLHS},
      {"a", ExprRole::kRHS},
      {"b", ExprRole::kRHS},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 3u);
}

TEST(ImplicitSensitivity, ConditionalExprWithTimingControl) {
  std::vector<VarRef> refs = {
      {"cond", ExprRole::kConditionalExpr},
      {"clk", ExprRole::kTimingControl},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "cond");
}

TEST(ImplicitSensitivity, LhsIndexWithTimingControl) {
  std::vector<VarRef> refs = {
      {"idx", ExprRole::kLHSIndex},
      {"clk", ExprRole::kTimingControl},
      {"out", ExprRole::kPureLHS},
  };
  auto result = ComputeImplicitSensitivity(refs);
  EXPECT_EQ(result.size(), 1u);
  EXPECT_EQ(result[0], "idx");
}

}  // namespace
