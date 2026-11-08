#pragma once

#include <cstdint>
#include <optional>
#include <string_view>

namespace delta {

enum class NotationCategory : std::uint8_t {
  kBooleanExpression,
  kType,
  kLocalVariableName,
  kFreeCheckerVariableName,
  kExpression,
  kUnclockedSequence,
  kClockedSequence,
  kUnclockedProperty,
  kClockedProperty,
  kUnclockedTopLevelProperty,
  kClockedTopLevelProperty,
  kSequence,
  kProperty,
  kAssertion,
  kNonNegativeIntegerConstant,
};

std::optional<NotationCategory> ClassifyAnnexFNotation(std::string_view symbol);

bool DenotesSequence(NotationCategory category);

bool DenotesProperty(NotationCategory category);

}  // namespace delta
