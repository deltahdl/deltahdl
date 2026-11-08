#ifndef DELTA_SIMULATOR_SEQUENCE_ACTUAL_CAST_H
#define DELTA_SIMULATOR_SEQUENCE_ACTUAL_CAST_H

#include "lexer/token.h"

namespace delta {

class Arena;
struct DataType;
struct Expr;

Expr* CastActualToFormal(Expr* actual, TokenKind type_kw, DataType* type,
                         Arena& arena);

}  // namespace delta

#endif
