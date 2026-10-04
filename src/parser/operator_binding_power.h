#pragma once

#include <utility>

#include "lexer/token.h"

namespace delta {

// §11.3.2 (Table 11-2): operator precedence and associativity, as the binding
// powers a Pratt parser reads. The pair is the left and right binding power of
// a binary operator: a higher power binds tighter, and a left power above the
// right one makes the operator group to the right. {-1, -1} for a token that is
// no binary operator. The expression parser parses by them, and a reader that
// rebuilds an expression's text reads them too, so the two cannot disagree.
std::pair<int, int> InfixBindingPower(TokenKind kind);

// §11.3.2 (Table 11-2): the binding power of a unary operator, tighter than
// every binary one; -1 for a token that is no unary operator.
int PrefixBindingPower(TokenKind kind);

}  // namespace delta
