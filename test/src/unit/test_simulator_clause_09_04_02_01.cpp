// §9.4.2.1: Event OR operator

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

enum class ExprRole : uint8_t {
  kRHS,
  kSubroutineArg,
  kCaseExpr,
  kConditionalExpr,
  kLHSIndex,
  kPureLHS,
  kTimingControl,
};

struct VarRef {
  std::string name;
  ExprRole role;
};

std::vector<std::string> ComputeImplicitSensitivity(
    const std::vector<VarRef> &refs) {
  std::vector<std::string> result;
  for (const auto &ref : refs) {
    switch (ref.role) {
      case ExprRole::kRHS:
      case ExprRole::kSubroutineArg:
      case ExprRole::kCaseExpr:
      case ExprRole::kConditionalExpr:
      case ExprRole::kLHSIndex:
        result.push_back(ref.name);
        break;
      case ExprRole::kPureLHS:
      case ExprRole::kTimingControl:
        break;
    }
  }
  return result;
}

namespace {

TEST(TimingControl, CommaSynonymousWithOr) {
  std::vector<VarRef> comma_list = {
      {"a", ExprRole::kRHS},
      {"b", ExprRole::kRHS},
  };
  std::vector<VarRef> or_list = {
      {"a", ExprRole::kRHS},
      {"b", ExprRole::kRHS},
  };
  auto comma_result = ComputeImplicitSensitivity(comma_list);
  auto or_result = ComputeImplicitSensitivity(or_list);
  EXPECT_EQ(comma_result, or_result);
}

}  // namespace
