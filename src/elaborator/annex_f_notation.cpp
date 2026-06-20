#include "elaborator/annex_f_notation.h"

#include <cctype>
#include <cstddef>
#include <optional>
#include <string_view>

namespace delta {

namespace {

// §F.3.3 says the conventions also cover subscripted versions of each
// notation, so a metavariable's category is taken from its base letter.
// Drop a trailing run of digits and one optional separating underscore so
// forms such as b1 or R_2 resolve to b and R.
std::string_view StripSubscript(std::string_view symbol) {
  std::size_t end = symbol.size();
  while (end > 0 && std::isdigit(static_cast<unsigned char>(symbol[end - 1]))) {
    --end;
  }
  if (end > 0 && end < symbol.size() && symbol[end - 1] == '_') {
    --end;
  }
  return symbol.substr(0, end);
}

}  // namespace

std::optional<NotationCategory> ClassifyAnnexFNotation(
    std::string_view symbol) {
  const std::string_view kBase = StripSubscript(symbol);
  if (kBase.size() != 1) {
    return std::nullopt;
  }
  switch (kBase[0]) {
    case 'b':
    case 'c':
      return NotationCategory::kBooleanExpression;
    case 't':
      return NotationCategory::kType;
    case 'v':
      return NotationCategory::kLocalVariableName;
    case 'u':
      return NotationCategory::kFreeCheckerVariableName;
    case 'e':
      return NotationCategory::kExpression;
    case 'R':
      return NotationCategory::kUnclockedSequence;
    case 'S':
      return NotationCategory::kClockedSequence;
    case 'P':
      return NotationCategory::kUnclockedProperty;
    case 'Q':
      return NotationCategory::kClockedProperty;
    case 'T':
      return NotationCategory::kUnclockedTopLevelProperty;
    case 'U':
      return NotationCategory::kClockedTopLevelProperty;
    case 'r':
    case 's':
      return NotationCategory::kSequence;
    case 'p':
    case 'q':
      return NotationCategory::kProperty;
    case 'A':
      return NotationCategory::kAssertion;
    case 'i':
    case 'j':
    case 'k':
    case 'm':
    case 'n':
      return NotationCategory::kNonNegativeIntegerConstant;
    default:
      return std::nullopt;
  }
}

bool DenotesSequence(NotationCategory category) {
  switch (category) {
    case NotationCategory::kUnclockedSequence:
    case NotationCategory::kClockedSequence:
    case NotationCategory::kSequence:
      return true;
    default:
      return false;
  }
}

bool DenotesProperty(NotationCategory category) {
  switch (category) {
    case NotationCategory::kUnclockedProperty:
    case NotationCategory::kClockedProperty:
    case NotationCategory::kUnclockedTopLevelProperty:
    case NotationCategory::kClockedTopLevelProperty:
    case NotationCategory::kProperty:
      return true;
    default:
      return false;
  }
}

}  // namespace delta
