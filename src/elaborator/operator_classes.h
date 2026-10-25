#pragma once

#include "lexer/token.h"

namespace delta {

// §11.6.1 Table 11-21 sorts the operators by how each sizes its result, and
// §11.8.1 follows the same classes for its sign. The run sizes an expression's
// operands by them, and $typename writes an expression's self-determined type
// by them, during the run and in a constant folded at elaboration.

// The arithmetic and bitwise binary operators, whose result is as wide as the
// wider of their two operands.
bool IsMaxWidthBinaryOp(TokenKind op);

// The shift and power operators, whose result is as wide as their left
// operand.
bool IsLeftWidthBinaryOp(TokenKind op);

// The unary reduction operators, whose result is one bit.
bool IsUnaryReductionOp(TokenKind op);

}  // namespace delta
