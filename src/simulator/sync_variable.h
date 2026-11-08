#pragma once

#include <string_view>

namespace delta {

class Arena;
struct RtlirVariable;
class SimContext;
struct Stmt;
struct Variable;

void CreateSyncObjectForVar(std::string_view name, const RtlirVariable& var,
                            Variable* v, SimContext& ctx, Arena& arena);

void HoldSyncVariable(std::string_view key, SimContext& ctx);

void CreateSyncObjectForLocal(const Stmt* stmt, Variable* v, SimContext& ctx,
                              Arena& arena);

bool TryLocalSyncNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

}  // namespace delta
