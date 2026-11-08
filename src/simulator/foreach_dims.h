#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"

namespace delta {

class Arena;
struct AssocArrayObject;
struct ClassArrayRef;
struct Expr;
struct QueueObject;
class SimContext;
struct Stmt;
struct StructFieldInfo;
struct Variable;

std::string GetForeachArrayName(const Expr* expr);

struct ForeachDim {
  std::string_view var;
  int64_t left = 0;
  bool descending = false;
  uint64_t size = 0;

  int64_t IndexAt(uint64_t pos) const {
    auto step = static_cast<int64_t>(pos);
    return descending ? left - step : left + step;
  }
};

std::vector<ForeachDim> DeclaredForeachDims(const Stmt* stmt, SimContext& ctx);

uint32_t ForeachArraySize(std::string_view name, SimContext& ctx);

struct ForeachElementDim {
  Variable* var = nullptr;
  const QueueObject* queue = nullptr;
  const AssocArrayObject* assoc = nullptr;
};

ForeachElementDim ForeachElementDimOf(const Stmt* stmt,
                                      const AssocArrayObject* aa,
                                      SimContext& ctx, Arena& arena);

const QueueObject* ForeachElementQueue(const ForeachElementDim& dim,
                                       const std::vector<Logic4Vec>& keys,
                                       uint32_t i, Arena& arena);

Logic4Vec ForeachElementIndex(const QueueObject& element, uint32_t p,
                              Arena& arena);

std::vector<ForeachDim> ClassArrayForeachDims(const Stmt* stmt,
                                              const ClassArrayRef& ref);

std::vector<ForeachDim> StructMemberForeachDims(const Stmt* stmt,
                                                const StructFieldInfo& member);

uint64_t ForeachCombinationCount(const std::vector<ForeachDim>& dims);

std::vector<Variable*> CreateForeachDimVars(const std::vector<ForeachDim>& dims,
                                            SimContext& ctx);

void SetForeachDimVars(const std::vector<ForeachDim>& dims,
                       const std::vector<Variable*>& vars, uint64_t n,
                       Arena& arena);

}  // namespace delta
