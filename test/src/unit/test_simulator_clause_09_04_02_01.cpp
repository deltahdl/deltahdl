// §9.4.2.1: Event OR operator

#include "helpers_sensitivity.h"

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
