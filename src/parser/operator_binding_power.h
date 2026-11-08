#pragma once

#include <utility>

#include "lexer/token.h"

namespace delta {

std::pair<int, int> InfixBindingPower(TokenKind kind);

int PrefixBindingPower(TokenKind kind);

}  // namespace delta
