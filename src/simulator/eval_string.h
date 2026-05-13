#pragma once

#include "common/types.h"

namespace delta {

struct Expr;
struct Variable;
class SimContext;
class Arena;

// §6.16: String method dispatch (eval_string.cpp).
bool TryEvalStringMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out);

// §6.16: Strip every '\0' byte from a byte-packed value, returning a new
// Logic4Vec sized to the kept-byte count.  An all-zero input collapses to a
// single zero byte (width 8) so callers can still address byte 0.
Logic4Vec StripStringZeros(const Logic4Vec& packed, Arena& arena);

// §6.16: Replace the byte at character index `idx` of a string variable with
// `byte_val`, where index 0 is the leftmost character.  Per §6.16 a zero
// byte is silently dropped; an out-of-range index leaves the variable
// unchanged.
void StringWriteByte(Variable* var, uint32_t idx, uint8_t byte_val,
                     Arena& arena);

}  // namespace delta
