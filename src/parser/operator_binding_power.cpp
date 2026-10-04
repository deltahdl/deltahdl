#include "parser/operator_binding_power.h"

#include <utility>

#include "lexer/token.h"

namespace delta {

std::pair<int, int> InfixBindingPower(TokenKind kind) {
  switch (kind) {
    case TokenKind::kPipeDashGt:
    case TokenKind::kPipeEqGt:
      return {1, 2};
    case TokenKind::kArrow:
    case TokenKind::kLtDashGt:
      return {2, 1};
    case TokenKind::kPipePipe:
      return {3, 4};
    case TokenKind::kAmpAmp:
      return {5, 6};
    case TokenKind::kPipe:
      return {7, 8};
    case TokenKind::kCaret:
    case TokenKind::kCaretTilde:
    case TokenKind::kTildeCaret:
      return {9, 10};
    case TokenKind::kAmp:
      return {11, 12};
    case TokenKind::kEqEq:
    case TokenKind::kBangEq:
    case TokenKind::kEqEqEq:
    case TokenKind::kBangEqEq:
    case TokenKind::kEqEqQuestion:
    case TokenKind::kBangEqQuestion:
      return {13, 14};
    case TokenKind::kLt:
    case TokenKind::kGt:
    case TokenKind::kLtEq:
    case TokenKind::kGtEq:
      return {15, 16};
    case TokenKind::kLtLt:
    case TokenKind::kGtGt:
    case TokenKind::kLtLtLt:
    case TokenKind::kGtGtGt:
      return {17, 18};
    case TokenKind::kPlus:
    case TokenKind::kMinus:
      return {19, 20};
    case TokenKind::kStar:
    case TokenKind::kSlash:
    case TokenKind::kPercent:
      return {21, 22};
    case TokenKind::kPower:
      return {23, 24};
    default:
      return {-1, -1};
  }
}

int PrefixBindingPower(TokenKind kind) {
  switch (kind) {
    case TokenKind::kPlus:
    case TokenKind::kMinus:
    case TokenKind::kBang:
    case TokenKind::kTilde:
    case TokenKind::kAmp:
    case TokenKind::kTildeAmp:
    case TokenKind::kPipe:
    case TokenKind::kTildePipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return 25;
    default:
      return -1;
  }
}

}  // namespace delta
