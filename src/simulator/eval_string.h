#pragma once

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

}  // namespace delta
