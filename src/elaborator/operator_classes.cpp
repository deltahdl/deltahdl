#include "elaborator/operator_classes.h"

#include "lexer/token.h"

namespace delta {

// §11.6.1 Table 11-21: arithmetic and bitwise operators whose result width is
// the maximum width of the two operands; both operands are context-determined.
bool IsMaxWidthBinaryOp(TokenKind op) {
  switch (op) {
    case TokenKind::kPlus:
    case TokenKind::kMinus:
    case TokenKind::kStar:
    case TokenKind::kSlash:
    case TokenKind::kPercent:
    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return true;
    default:
      return false;
  }
}

// §11.6.1: shift and power operators whose result width is the left operand's
// width; the left operand is context-determined, the right self-determined.
bool IsLeftWidthBinaryOp(TokenKind op) {
  switch (op) {
    case TokenKind::kPower:
    case TokenKind::kLtLt:
    case TokenKind::kGtGt:
    case TokenKind::kLtLtLt:
    case TokenKind::kGtGtGt:
      return true;
    default:
      return false;
  }
}

// §11.6.1: the unary reduction operators, whose result is one bit.
bool IsUnaryReductionOp(TokenKind op) {
  switch (op) {
    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeAmp:
    case TokenKind::kTildePipe:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return true;
    default:
      return false;
  }
}

}  // namespace delta
