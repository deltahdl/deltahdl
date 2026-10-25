#ifndef DELTA_SIMULATOR_SEQUENCE_ACTUAL_CAST_H
#define DELTA_SIMULATOR_SEQUENCE_ACTUAL_CAST_H

#include "lexer/token.h"

namespace delta {

class Arena;
struct DataType;
struct Expr;

// §16.8 and §16.8.1 (c): the actual an instance of a named sequence or
// property binds to a formal recorded with the type keyword `type_kw` and
// the data type `type`, as it stands for the formal: cast to the keyword's
// type, with the signing `type` holds, for a keyword data type, to its own
// self-determined type for an untyped formal (SelfDeterminedActual), to
// `type` for a type no keyword alone names, which a formal whose `type_kw`
// is kEof always holds, and
// otherwise as written: a `$`, an event actual, or one bound to a formal of
// the sequence, property or event type.
Expr* CastActualToFormal(Expr* actual, TokenKind type_kw, DataType* type,
                         Arena& arena);

}  // namespace delta

#endif  // DELTA_SIMULATOR_SEQUENCE_ACTUAL_CAST_H
