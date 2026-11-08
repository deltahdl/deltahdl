#pragma once

#include "lexer/token.h"

namespace delta {

bool IsMaxWidthBinaryOp(TokenKind op);

bool IsLeftWidthBinaryOp(TokenKind op);

bool IsUnaryReductionOp(TokenKind op);

}  // namespace delta
