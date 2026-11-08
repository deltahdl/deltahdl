#pragma once

#include <cstdint>
#include <string_view>

namespace delta {

class Arena;
struct ClassTypeInfo;
struct DataType;
struct Expr;
class SimContext;

DataType TypeSpelledBy(const Expr* elem);

void BindClassScopeTypeActuals(const ClassTypeInfo* cls, const Expr* base,
                               SimContext& ctx, Arena& arena);

void BindStaticInitTypeActuals(const ClassTypeInfo* cls, SimContext& ctx);

uint32_t ScopedTypeParamWidth(std::string_view name, SimContext& ctx);

uint32_t SpecializationTypeParamWidth(const Expr* scope, SimContext& ctx,
                                      Arena& arena);

}  // namespace delta
