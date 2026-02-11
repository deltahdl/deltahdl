#include "simulation/eval_array.h"

#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

namespace delta {

// --- Helpers ---

// Collect all element values from an unpacked array into a vector.
static std::vector<uint64_t> CollectElements(std::string_view var_name,
                                             const ArrayInfo& info,
                                             SimContext& ctx) {
  std::vector<uint64_t> vals;
  vals.reserve(info.size);
  for (uint32_t i = 0; i < info.size; ++i) {
    uint32_t idx = info.lo + i;
    auto name = std::string(var_name) + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(name);
    vals.push_back(v ? v->value.ToUint64() : 0);
  }
  return vals;
}

// Write element values back to an unpacked array.
static void WriteElements(std::string_view var_name, const ArrayInfo& info,
                          const std::vector<uint64_t>& vals, SimContext& ctx,
                          Arena& arena) {
  for (uint32_t i = 0; i < info.size && i < vals.size(); ++i) {
    uint32_t idx = info.lo + i;
    auto name = std::string(var_name) + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(name);
    if (v) v->value = MakeLogic4VecVal(arena, info.elem_width, vals[i]);
  }
}

// --- Reduction methods (§7.12.3) ---

static Logic4Vec ArraySum(std::string_view var_name, const ArrayInfo& info,
                          SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  uint64_t result = 0;
  for (auto v : vals) result += v;
  return MakeLogic4VecVal(arena, 32, result);
}

static Logic4Vec ArrayProduct(std::string_view var_name, const ArrayInfo& info,
                              SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  uint64_t result = 1;
  for (auto v : vals) result *= v;
  return MakeLogic4VecVal(arena, 32, result);
}

static Logic4Vec ArrayAnd(std::string_view var_name, const ArrayInfo& info,
                          SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  uint64_t result = vals.empty() ? 0 : vals[0];
  for (size_t i = 1; i < vals.size(); ++i) result &= vals[i];
  return MakeLogic4VecVal(arena, info.elem_width, result);
}

static Logic4Vec ArrayOr(std::string_view var_name, const ArrayInfo& info,
                         SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  uint64_t result = 0;
  for (auto v : vals) result |= v;
  return MakeLogic4VecVal(arena, info.elem_width, result);
}

static Logic4Vec ArrayXor(std::string_view var_name, const ArrayInfo& info,
                          SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  uint64_t result = 0;
  for (auto v : vals) result ^= v;
  return MakeLogic4VecVal(arena, info.elem_width, result);
}

// --- Size method ---

static Logic4Vec ArraySize(const ArrayInfo& info, Arena& arena) {
  return MakeLogic4VecVal(arena, 32, info.size);
}

// --- Locator methods (§7.12.1) ---

static Logic4Vec ArrayMin(std::string_view var_name, const ArrayInfo& info,
                          SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  if (vals.empty()) return MakeLogic4VecVal(arena, info.elem_width, 0);
  uint64_t result = *std::min_element(vals.begin(), vals.end());
  return MakeLogic4VecVal(arena, info.elem_width, result);
}

static Logic4Vec ArrayMax(std::string_view var_name, const ArrayInfo& info,
                          SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  if (vals.empty()) return MakeLogic4VecVal(arena, info.elem_width, 0);
  uint64_t result = *std::max_element(vals.begin(), vals.end());
  return MakeLogic4VecVal(arena, info.elem_width, result);
}

// --- Dispatch ---

// §7.12.3: Reduction method dispatch.
static bool DispatchReduction(std::string_view method,
                              std::string_view var_name, const ArrayInfo& info,
                              SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (method == "sum") {
    out = ArraySum(var_name, info, ctx, arena);
    return true;
  }
  if (method == "product") {
    out = ArrayProduct(var_name, info, ctx, arena);
    return true;
  }
  if (method == "and") {
    out = ArrayAnd(var_name, info, ctx, arena);
    return true;
  }
  if (method == "or") {
    out = ArrayOr(var_name, info, ctx, arena);
    return true;
  }
  if (method == "xor") {
    out = ArrayXor(var_name, info, ctx, arena);
    return true;
  }
  return false;
}

// §7.12.1: Locator and query method dispatch.
static bool DispatchQuery(std::string_view method, std::string_view var_name,
                          const ArrayInfo& info, SimContext& ctx, Arena& arena,
                          Logic4Vec& out) {
  if (method == "size") {
    out = ArraySize(info, arena);
    return true;
  }
  if (method == "min") {
    out = ArrayMin(var_name, info, ctx, arena);
    return true;
  }
  if (method == "max") {
    out = ArrayMax(var_name, info, ctx, arena);
    return true;
  }
  return false;
}

bool TryEvalArrayMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  auto* info = ctx.FindArrayInfo(parts.var_name);
  if (!info) return false;
  if (DispatchReduction(parts.method_name, parts.var_name, *info, ctx, arena,
                        out)) {
    return true;
  }
  if (DispatchQuery(parts.method_name, parts.var_name, *info, ctx, arena,
                    out)) {
    return true;
  }
  // Mutating methods return void; set out to 0 on success.
  if (TryExecArrayMethodStmt(expr, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  return false;
}

// --- Mutating methods (§7.12.2) ---

static void ArraySort(std::string_view var_name, const ArrayInfo& info,
                      SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  std::sort(vals.begin(), vals.end());
  WriteElements(var_name, info, vals, ctx, arena);
}

static void ArrayRsort(std::string_view var_name, const ArrayInfo& info,
                       SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  std::sort(vals.begin(), vals.end(), std::greater<>());
  WriteElements(var_name, info, vals, ctx, arena);
}

static void ArrayReverse(std::string_view var_name, const ArrayInfo& info,
                         SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  std::reverse(vals.begin(), vals.end());
  WriteElements(var_name, info, vals, ctx, arena);
}

static void ArrayShuffle(std::string_view var_name, const ArrayInfo& info,
                         SimContext& ctx, Arena& arena) {
  auto vals = CollectElements(var_name, info, ctx);
  // Use a simple shuffle (std::shuffle requires a URBG).
  for (size_t i = vals.size(); i > 1; --i) {
    size_t j = ctx.Urandom32() % i;
    std::swap(vals[i - 1], vals[j]);
  }
  WriteElements(var_name, info, vals, ctx, arena);
}

bool TryExecArrayMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  auto* info = ctx.FindArrayInfo(parts.var_name);
  if (!info) return false;
  if (parts.method_name == "sort") {
    ArraySort(parts.var_name, *info, ctx, arena);
    return true;
  }
  if (parts.method_name == "rsort") {
    ArrayRsort(parts.var_name, *info, ctx, arena);
    return true;
  }
  if (parts.method_name == "reverse") {
    ArrayReverse(parts.var_name, *info, ctx, arena);
    return true;
  }
  if (parts.method_name == "shuffle") {
    ArrayShuffle(parts.var_name, *info, ctx, arena);
    return true;
  }
  return false;
}

// §7.12: Property access (e.g., arr.sum without parens).
bool TryEvalArrayProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out) {
  auto* info = ctx.FindArrayInfo(var_name);
  if (!info) return false;
  if (DispatchReduction(prop, var_name, *info, ctx, arena, out)) return true;
  return DispatchQuery(prop, var_name, *info, ctx, arena, out);
}

// §7.12: Mutating property access (arr.sort, arr.reverse).
bool TryExecArrayPropertyStmt(std::string_view var_name, std::string_view prop,
                              SimContext& ctx, Arena& arena) {
  auto* info = ctx.FindArrayInfo(var_name);
  if (!info) return false;
  if (prop == "sort") {
    ArraySort(var_name, *info, ctx, arena);
    return true;
  }
  if (prop == "rsort") {
    ArrayRsort(var_name, *info, ctx, arena);
    return true;
  }
  if (prop == "reverse") {
    ArrayReverse(var_name, *info, ctx, arena);
    return true;
  }
  if (prop == "shuffle") {
    ArrayShuffle(var_name, *info, ctx, arena);
    return true;
  }
  return false;
}

}  // namespace delta
