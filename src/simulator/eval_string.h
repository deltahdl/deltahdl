#pragma once

#include <cstdint>
#include <string_view>

#include "common/types.h"

namespace delta {

struct Expr;
struct Variable;
class SimContext;
class Arena;

bool TryEvalStringMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out);

bool TryEvalStringProperty(std::string_view var_name, std::string_view prop,
                           SimContext& ctx, Arena& arena, Logic4Vec& out);

Logic4Vec StripStringZeros(const Logic4Vec& packed, Arena& arena);

void StringWriteByte(Variable* var, uint32_t idx, uint8_t byte_val,
                     Arena& arena);

// §6.16 (printed page 113): the indexed character assignment `s[i] = c` on a
// string that is a class property rather than a variable of the run's tables
// -- `h.p[0] = "x"` through a handle, `p[0] = "x"` bare or through `this`
// inside a method of the class, `C::name[0] = "N"` on a static property --
// replacing the character the index addresses in the property's text. True
// when `lhs` selects one index of such a property, the write then made or,
// for an index out of range, an unknown index or a null character, withheld
// as StringWriteByte withholds it; false for any other target.
bool TryWriteStringPropertyChar(const Expr* lhs, const Logic4Vec& rhs_val,
                                SimContext& ctx, Arena& arena);

}  // namespace delta
