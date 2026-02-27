#pragma once

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

inline std::vector<std::string> ComputeImplicitSensitivity(
    const std::vector<VarRef>& refs) {
  std::vector<std::string> result;
  for (const auto& ref : refs) {
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
