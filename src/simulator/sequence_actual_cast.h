#ifndef DELTA_SIMULATOR_SEQUENCE_ACTUAL_CAST_H
#define DELTA_SIMULATOR_SEQUENCE_ACTUAL_CAST_H

#include "lexer/token.h"

namespace delta {

class Arena;
class SimContext;
struct Expr;

// §16.8 and §16.8.1 (c): the actual an instance of a named sequence or
// property binds to a formal recorded with the type keyword `type_kw`, as it
// stands for the formal: cast to the keyword's type for a keyword data type,
// cast to its own self-determined type for an untyped formal, and otherwise
// as written.
Expr* CastActualToFormal(Expr* actual, TokenKind type_kw, SimContext& ctx,
                         Arena& arena);

}  // namespace delta

#endif  // DELTA_SIMULATOR_SEQUENCE_ACTUAL_CAST_H
