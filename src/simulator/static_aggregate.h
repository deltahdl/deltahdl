#pragma once

#include <string_view>

namespace delta {

class Arena;
class SimContext;
struct Stmt;

void RetainStaticAggregate(std::string_view frame, std::string_view name,
                           SimContext& ctx, Arena& arena);
bool RestoreStaticAggregate(std::string_view frame, std::string_view name,
                            SimContext& ctx);

bool IsEffectivelyStaticLocal(const Stmt* stmt, std::string_view func_name,
                              SimContext& ctx);

bool IsAutomaticLocal(const Stmt& stmt, SimContext& ctx);

void RetainBlockAggregates(const Stmt& block, std::string_view frame,
                           SimContext& ctx, Arena& arena);
void RestoreBlockAggregates(const Stmt& block, std::string_view frame,
                            SimContext& ctx);

}  // namespace delta
