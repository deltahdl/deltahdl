#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"
#include "simulator/class_object.h"

namespace delta {

struct Expr;
struct Stmt;
class SimContext;
class Arena;

std::string ClassArrayElementKey(std::string_view name, int64_t index);

std::string ClassArraySizeKey(std::string_view name);

void DropDroppedElementModes(std::unordered_map<std::string, bool>& modes,
                             std::string_view member, int64_t size);

const ClassTypeInfo::PropertyInfo* FindClassArrayProperty(
    const ClassTypeInfo* type, std::string_view name);

struct ClassArrayRef {
  ClassObject* obj = nullptr;
  const ClassTypeInfo::PropertyInfo* prop = nullptr;
  bool bare = false;
  uint32_t size = 0;
  int64_t lo = 0;
  const ClassTypeInfo* static_owner = nullptr;
  std::string path = {};
  uint32_t dim = 0;
};

std::string ClassArrayRefElementKey(const ClassArrayRef& ref, int64_t index);

bool ClassArrayHoldsSubarrays(const ClassArrayRef& ref);

uint32_t ClassArraySize(const ClassObject* obj,
                        const ClassTypeInfo::PropertyInfo& prop);

void ResizeClassArray(const ClassArrayRef& ref, uint32_t size,
                      const ClassArrayRef* init, SimContext& ctx, Arena& arena);

bool ResolveClassArray(const Expr* base, SimContext& ctx, Arena& arena,
                       ClassArrayRef& out);

Logic4Vec ReadClassArrayElement(const ClassArrayRef& ref, int64_t index,
                                SimContext& ctx, Arena& arena);

bool TryClassArrayElementSelect(const Expr* expr, int64_t index,
                                SimContext& ctx, Arena& arena, Logic4Vec& out);

bool TryEvalClassArrayMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

bool TryClassArrayNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

bool PropertyArrayElements(const Expr* src, SimContext& ctx, Arena& arena,
                           std::vector<Logic4Vec>& out);

bool StoreClassArrayPattern(const ClassArrayRef& dst_ref, const Expr* rhs,
                            SimContext& ctx, Arena& arena);

bool TryClassArrayWholeAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

bool NamesOwnArrayProperty(const Expr* base, SimContext& ctx);

void StoreClassArrayElement(const ClassArrayRef& ref, int64_t index,
                            const Logic4Vec& value, SimContext& ctx,
                            Arena& arena);

bool TryWriteClassArrayElementChar(const Expr* lhs, const Logic4Vec& rhs_val,
                                   SimContext& ctx, Arena& arena);

bool TryWriteClassArrayElementBits(const Expr* lhs, const Logic4Vec& rhs_val,
                                   SimContext& ctx, Arena& arena);

bool TryWriteClassArrayElement(const Expr* lhs, const Logic4Vec& rhs_val,
                               SimContext& ctx, Arena& arena);

}  // namespace delta
