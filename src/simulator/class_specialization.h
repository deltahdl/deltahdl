#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "elaborator/const_eval.h"

namespace delta {

class Arena;
class SimContext;
struct ClassTypeInfo;
struct DataType;
struct Expr;

struct PropertyArrayDim {
  uint32_t size = 0;
  int64_t lo = 0;
  bool descending = false;
};

PropertyArrayDim FoldPropertyDimension(const Expr* dim, const ScopeMap& scope,
                                       SimContext& ctx, Arena& arena);

ClassTypeInfo* SpecializationOf(ClassTypeInfo* generic,
                                const std::vector<DataType>& actuals,
                                SimContext& ctx, Arena& arena);

void BindDeclarationBase(ClassTypeInfo* info, SimContext& ctx, Arena& arena);

std::vector<DataType> ActualsUnderSpecialization(
    const ClassTypeInfo* holder, const std::vector<DataType>& written,
    SimContext& ctx);

ClassTypeInfo* ClassNamedByTypeParam(std::string_view name, SimContext& ctx,
                                     Arena& arena);

void InitSpecializationStaticProperties(ClassTypeInfo* spec, SimContext& ctx,
                                        Arena& arena);

ClassTypeInfo* ScopeNamedSpecialization(const Expr* base, SimContext& ctx,
                                        Arena& arena);

bool TryScopeSpecializationStaticMember(const Expr* expr, SimContext& ctx,
                                        Arena& arena, Logic4Vec& out);

const DataType* RunningTypeActual(std::string_view name, SimContext& ctx);

}  // namespace delta
