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
  if (info.is_dynamic) {
    auto* q = ctx.FindQueue(var_name);
    if (!q) return {};
    std::vector<uint64_t> vals;
    vals.reserve(q->elements.size());
    for (const auto& e : q->elements) vals.push_back(e.ToUint64());
    return vals;
  }
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
  if (info.is_dynamic) {
    auto* q = ctx.FindQueue(var_name);
    if (!q) return;
    q->elements.resize(vals.size());
    for (size_t i = 0; i < vals.size(); ++i)
      q->elements[i] = MakeLogic4VecVal(arena, q->elem_width, vals[i]);
    ++q->generation;
    return;
  }
  for (uint32_t i = 0; i < info.size && i < vals.size(); ++i) {
    uint32_t idx = info.lo + i;
    auto name = std::string(var_name) + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(name);
    if (v) v->value = MakeLogic4VecVal(arena, info.elem_width, vals[i]);
  }
}

// Collect Logic4Vec values from an unpacked array (preserves full value).
static std::vector<Logic4Vec> CollectVecElements(std::string_view var_name,
                                                 const ArrayInfo& info,
                                                 SimContext& ctx,
                                                 Arena& arena) {
  if (info.is_dynamic) {
    auto* q = ctx.FindQueue(var_name);
    if (!q) return {};
    return q->elements;
  }
  std::vector<Logic4Vec> vals;
  vals.reserve(info.size);
  for (uint32_t i = 0; i < info.size; ++i) {
    uint32_t idx = info.lo + i;
    auto name = std::string(var_name) + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(name);
    vals.push_back(v ? v->value : MakeLogic4VecVal(arena, info.elem_width, 0));
  }
  return vals;
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

static Logic4Vec ArraySize(std::string_view var_name, const ArrayInfo& info,
                           SimContext& ctx, Arena& arena) {
  if (info.is_dynamic) {
    auto* q = ctx.FindQueue(var_name);
    return MakeLogic4VecVal(arena, 32, q ? q->elements.size() : 0);
  }
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

// Bundles common array method arguments to stay within 5-parameter limit.
struct ArrayCtx {
  std::string_view var_name;
  const ArrayInfo& info;
  SimContext& ctx;
  Arena& arena;
};

// §7.12.3: Reduction method dispatch.
static bool DispatchReduction(std::string_view method, const ArrayCtx& ac,
                              Logic4Vec& out) {
  if (method == "sum") {
    out = ArraySum(ac.var_name, ac.info, ac.ctx, ac.arena);
    return true;
  }
  if (method == "product") {
    out = ArrayProduct(ac.var_name, ac.info, ac.ctx, ac.arena);
    return true;
  }
  if (method == "and") {
    out = ArrayAnd(ac.var_name, ac.info, ac.ctx, ac.arena);
    return true;
  }
  if (method == "or") {
    out = ArrayOr(ac.var_name, ac.info, ac.ctx, ac.arena);
    return true;
  }
  if (method == "xor") {
    out = ArrayXor(ac.var_name, ac.info, ac.ctx, ac.arena);
    return true;
  }
  return false;
}

// §7.12.1: Locator and query method dispatch.
static bool DispatchQuery(std::string_view method, const ArrayCtx& ac,
                          Logic4Vec& out) {
  if (method == "size") {
    out = ArraySize(ac.var_name, ac.info, ac.ctx, ac.arena);
    return true;
  }
  if (method == "min") {
    out = ArrayMin(ac.var_name, ac.info, ac.ctx, ac.arena);
    return true;
  }
  if (method == "max") {
    out = ArrayMax(ac.var_name, ac.info, ac.ctx, ac.arena);
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
  ArrayCtx ac{parts.var_name, *info, ctx, arena};
  if (DispatchReduction(parts.method_name, ac, out)) return true;
  if (DispatchQuery(parts.method_name, ac, out)) return true;
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

// Write Logic4Vec values back to an unpacked array (preserves width).
static void WriteVecElements(std::string_view var_name, const ArrayInfo& info,
                             const std::vector<Logic4Vec>& vals,
                             SimContext& ctx) {
  if (info.is_dynamic) {
    auto* q = ctx.FindQueue(var_name);
    if (!q) return;
    q->elements.resize(vals.size());
    for (size_t i = 0; i < vals.size(); ++i) q->elements[i] = vals[i];
    ++q->generation;
    return;
  }
  for (uint32_t i = 0; i < info.size && i < vals.size(); ++i) {
    uint32_t idx = info.lo + i;
    auto name = std::string(var_name) + "[" + std::to_string(idx) + "]";
    auto* v = ctx.FindVariable(name);
    if (v) v->value = vals[i];
  }
}

static void ArrayReverse(std::string_view var_name, const ArrayInfo& info,
                         SimContext& ctx, Arena& arena) {
  auto vals = CollectVecElements(var_name, info, ctx, arena);
  std::reverse(vals.begin(), vals.end());
  WriteVecElements(var_name, info, vals, ctx);
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
  ArrayCtx ac{var_name, *info, ctx, arena};
  if (DispatchReduction(prop, ac, out)) return true;
  return DispatchQuery(prop, ac, out);
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

// --- §7.10: Queue method dispatch ---

// §7.10.2: Eval-returning queue methods (size, pop_front, pop_back).
static bool DispatchQueueEval(std::string_view method, QueueObject* q,
                              Arena& arena, Logic4Vec& out) {
  if (method == "size") {
    out = MakeLogic4VecVal(arena, 32, q->elements.size());
    return true;
  }
  if (method == "pop_front") {
    if (q->elements.empty()) {
      out = MakeLogic4VecVal(arena, q->elem_width, 0);
    } else {
      out = q->elements.front();
      q->elements.erase(q->elements.begin());
      if (!q->element_ids.empty()) q->element_ids.erase(q->element_ids.begin());
      ++q->generation;
    }
    return true;
  }
  if (method == "pop_back") {
    if (q->elements.empty()) {
      out = MakeLogic4VecVal(arena, q->elem_width, 0);
    } else {
      out = q->elements.back();
      q->elements.pop_back();
      if (!q->element_ids.empty()) q->element_ids.pop_back();
      ++q->generation;
    }
    return true;
  }
  return false;
}

// §7.10.2: Queue push/insert methods.
static bool DispatchQueuePush(std::string_view method, QueueObject* q,
                              const Expr* expr, SimContext& ctx, Arena& arena) {
  if (method == "push_back" && !expr->args.empty()) {
    auto val = EvalExpr(expr->args[0], ctx, arena);
    bool has_room = (q->max_size < 0) ||
                    (static_cast<int32_t>(q->elements.size()) < q->max_size);
    if (has_room) {
      q->elements.push_back(val);
      q->element_ids.push_back(q->AllocateId());
      ++q->generation;
    }
    return true;
  }
  if (method == "push_front" && !expr->args.empty()) {
    auto val = EvalExpr(expr->args[0], ctx, arena);
    bool has_room = (q->max_size < 0) ||
                    (static_cast<int32_t>(q->elements.size()) < q->max_size);
    if (has_room) {
      q->elements.insert(q->elements.begin(), val);
      q->element_ids.insert(q->element_ids.begin(), q->AllocateId());
      ++q->generation;
    }
    return true;
  }
  if (method == "insert" && expr->args.size() >= 2) {
    auto idx =
        static_cast<size_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
    auto val = EvalExpr(expr->args[1], ctx, arena);
    if (idx <= q->elements.size()) {
      q->elements.insert(q->elements.begin() + static_cast<ptrdiff_t>(idx),
                         val);
      q->element_ids.insert(
          q->element_ids.begin() + static_cast<ptrdiff_t>(idx),
          q->AllocateId());
      ++q->generation;
    }
    return true;
  }
  return false;
}

// §7.10.2: Queue delete method.
static bool DispatchQueueDelete(std::string_view method, QueueObject* q,
                                const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (method != "delete") return false;
  if (!expr->args.empty()) {
    auto idx =
        static_cast<size_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
    if (idx < q->elements.size()) {
      q->elements.erase(q->elements.begin() + static_cast<ptrdiff_t>(idx));
      if (idx < q->element_ids.size())
        q->element_ids.erase(q->element_ids.begin() +
                             static_cast<ptrdiff_t>(idx));
      ++q->generation;
    }
  } else {
    q->elements.clear();
    q->element_ids.clear();
    ++q->generation;
  }
  return true;
}

bool TryEvalQueueMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  auto* q = ctx.FindQueue(parts.var_name);
  if (!q) return false;
  if (DispatchQueueEval(parts.method_name, q, arena, out)) return true;
  // Mutating methods also return via out (e.g., pop used in expression).
  if (DispatchQueuePush(parts.method_name, q, expr, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (DispatchQueueDelete(parts.method_name, q, expr, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  return false;
}

bool TryExecQueueMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  auto* q = ctx.FindQueue(parts.var_name);
  if (!q) return false;
  if (DispatchQueuePush(parts.method_name, q, expr, ctx, arena)) return true;
  return DispatchQueueDelete(parts.method_name, q, expr, ctx, arena);
}

bool TryEvalQueueProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out) {
  auto* q = ctx.FindQueue(var_name);
  if (!q) return false;
  // Use the same dispatch as method calls for eval-returning methods.
  return DispatchQueueEval(prop, q, arena, out);
}

// §7.10.3: Sort queue elements and IDs together, preserving ID-element pairing.
static void SortQueueWithIds(QueueObject* q, bool ascending) {
  auto& elems = q->elements;
  auto& ids = q->element_ids;
  std::vector<size_t> order(elems.size());
  for (size_t i = 0; i < order.size(); ++i) order[i] = i;
  std::sort(order.begin(), order.end(), [&](size_t a, size_t b) {
    return ascending ? elems[a].ToUint64() < elems[b].ToUint64()
                     : elems[a].ToUint64() > elems[b].ToUint64();
  });
  std::vector<Logic4Vec> sorted_elems(elems.size());
  std::vector<uint64_t> sorted_ids(ids.size());
  for (size_t i = 0; i < order.size(); ++i) {
    sorted_elems[i] = elems[order[i]];
    if (i < ids.size()) sorted_ids[i] = ids[order[i]];
  }
  elems = std::move(sorted_elems);
  ids = std::move(sorted_ids);
  ++q->generation;
}

// §7.10.3: Shuffle queue elements and IDs together.
static void ShuffleQueueWithIds(QueueObject* q, SimContext& ctx) {
  auto& elems = q->elements;
  auto& ids = q->element_ids;
  for (size_t i = elems.size(); i > 1; --i) {
    size_t j = ctx.Urandom32() % i;
    std::swap(elems[i - 1], elems[j]);
    if (i - 1 < ids.size() && j < ids.size()) std::swap(ids[i - 1], ids[j]);
  }
  ++q->generation;
}

bool TryExecQueuePropertyStmt(std::string_view var_name, std::string_view prop,
                              SimContext& ctx, Arena& /*arena*/) {
  auto* q = ctx.FindQueue(var_name);
  if (!q) return false;
  if (prop == "delete") {
    q->elements.clear();
    q->element_ids.clear();
    ++q->generation;
    return true;
  }
  if (prop == "sort") {
    SortQueueWithIds(q, true);
    return true;
  }
  if (prop == "rsort") {
    SortQueueWithIds(q, false);
    return true;
  }
  if (prop == "reverse") {
    std::reverse(q->elements.begin(), q->elements.end());
    std::reverse(q->element_ids.begin(), q->element_ids.end());
    ++q->generation;
    return true;
  }
  if (prop == "shuffle") {
    ShuffleQueueWithIds(q, ctx);
    return true;
  }
  return false;
}

// ============================================================================
// §7.8: Associative array method dispatch
// ============================================================================

// Convert Logic4Vec to a string (for string-keyed assoc array lookups).
static std::string Vec2Str(const Logic4Vec& vec) {
  uint32_t nbytes = vec.width / 8;
  std::string result;
  result.reserve(nbytes);
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    auto ch = static_cast<char>((vec.words[word].aval >> bit) & 0xFF);
    if (ch != 0) result.push_back(ch);
  }
  return result;
}

// Convert a string to a Logic4Vec (for writing string keys to ref vars).
static Logic4Vec Str2Vec(const std::string& s, Arena& arena) {
  uint32_t w = static_cast<uint32_t>(s.size()) * 8;
  if (w == 0) w = 8;
  auto vec = MakeLogic4Vec(arena, w);
  for (size_t i = 0; i < s.size(); ++i) {
    auto byte_idx = static_cast<uint32_t>(s.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    vec.words[word].aval |= static_cast<uint64_t>(s[i]) << bit;
  }
  return vec;
}

// Evaluate an assoc array key from an expression.
static std::string EvalStrKey(const Expr* expr, SimContext& ctx, Arena& arena) {
  return Vec2Str(EvalExpr(expr, ctx, arena));
}

static int64_t EvalIntKey(const Expr* expr, SimContext& ctx, Arena& arena) {
  return static_cast<int64_t>(EvalExpr(expr, ctx, arena).ToUint64());
}

// §7.8.1: exists(key).
static bool AssocExists(AssocArrayObject* aa, const Expr* expr, SimContext& ctx,
                        Arena& arena, Logic4Vec& out) {
  if (expr->args.empty()) return false;
  uint64_t found = 0;
  if (aa->is_string_key) {
    found = aa->str_data.count(EvalStrKey(expr->args[0], ctx, arena)) ? 1 : 0;
  } else {
    found = aa->int_data.count(EvalIntKey(expr->args[0], ctx, arena)) ? 1 : 0;
  }
  out = MakeLogic4VecVal(arena, 1, found);
  return true;
}

// §7.8.6: Traversal on string-keyed assoc arrays.
static bool AssocStrTraversal(AssocArrayObject* aa, std::string_view method,
                              Variable* ref_var, Arena& arena, Logic4Vec& out) {
  auto& m = aa->str_data;
  if (m.empty()) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }
  if (method == "first") {
    ref_var->value = Str2Vec(m.begin()->first, arena);
    out = MakeLogic4VecVal(arena, 32, 1);
    return true;
  }
  if (method == "last") {
    ref_var->value = Str2Vec(m.rbegin()->first, arena);
    out = MakeLogic4VecVal(arena, 32, 1);
    return true;
  }
  auto cur_key = Vec2Str(ref_var->value);
  auto it = m.find(cur_key);
  if (it == m.end()) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }
  if (method == "next") {
    ++it;
    if (it == m.end()) {
      out = MakeLogic4VecVal(arena, 32, 0);
      return true;
    }
    ref_var->value = Str2Vec(it->first, arena);
  } else {
    if (it == m.begin()) {
      out = MakeLogic4VecVal(arena, 32, 0);
      return true;
    }
    --it;
    ref_var->value = Str2Vec(it->first, arena);
  }
  out = MakeLogic4VecVal(arena, 32, 1);
  return true;
}

// §7.9.8: Write a traversal key, returning -1 if truncation is needed.
static int WriteTraversalKey(Variable* ref, int64_t key, uint32_t idx_width,
                             Arena& arena) {
  uint32_t w = ref->value.width;
  if (w == 0) w = 32;
  ref->value = MakeLogic4VecVal(arena, w, static_cast<uint64_t>(key));
  return (w < idx_width) ? -1 : 1;
}

// §7.8.6: Traversal on integer-keyed assoc arrays.
static bool AssocIntTraversal(AssocArrayObject* aa, std::string_view method,
                              Variable* ref_var, Arena& arena, Logic4Vec& out) {
  auto& m = aa->int_data;
  if (m.empty()) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }
  if (method == "first") {
    auto r =
        WriteTraversalKey(ref_var, m.begin()->first, aa->index_width, arena);
    out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(r));
    return true;
  }
  if (method == "last") {
    auto r =
        WriteTraversalKey(ref_var, m.rbegin()->first, aa->index_width, arena);
    out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(r));
    return true;
  }
  auto cur_key = static_cast<int64_t>(ref_var->value.ToUint64());
  auto it = m.find(cur_key);
  if (it == m.end()) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }
  if (method == "next") {
    ++it;
    if (it == m.end()) {
      out = MakeLogic4VecVal(arena, 32, 0);
      return true;
    }
  } else {
    if (it == m.begin()) {
      out = MakeLogic4VecVal(arena, 32, 0);
      return true;
    }
    --it;
  }
  auto r = WriteTraversalKey(ref_var, it->first, aa->index_width, arena);
  out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(r));
  return true;
}

// Resolve the ref argument for traversal methods.
static Variable* ResolveTraversalRef(const Expr* expr, SimContext& ctx) {
  if (expr->args.empty()) return nullptr;
  auto* ref_expr = expr->args[0];
  if (ref_expr->kind != ExprKind::kIdentifier) return nullptr;
  return ctx.FindVariable(ref_expr->text);
}

// §7.8.6: first/last/next/prev — dispatch to string or int traversal.
static bool AssocTraversal(AssocArrayObject* aa, std::string_view method,
                           Variable* ref_var, Arena& arena, Logic4Vec& out) {
  if (aa->is_string_key)
    return AssocStrTraversal(aa, method, ref_var, arena, out);
  return AssocIntTraversal(aa, method, ref_var, arena, out);
}

bool TryEvalAssocMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  auto* aa = ctx.FindAssocArray(parts.var_name);
  if (!aa) return false;
  if (parts.method_name == "size" || parts.method_name == "num") {
    out = MakeLogic4VecVal(arena, 32, aa->Size());
    return true;
  }
  if (parts.method_name == "exists")
    return AssocExists(aa, expr, ctx, arena, out);
  if (parts.method_name == "delete") {
    TryExecAssocMethodStmt(expr, ctx, arena);
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (parts.method_name == "first" || parts.method_name == "last" ||
      parts.method_name == "next" || parts.method_name == "prev") {
    auto* ref_var = ResolveTraversalRef(expr, ctx);
    if (!ref_var) {
      out = MakeLogic4VecVal(arena, 32, 0);
      return true;
    }
    return AssocTraversal(aa, parts.method_name, ref_var, arena, out);
  }
  return false;
}

static bool ExecAssocDelete(AssocArrayObject* aa, const Expr* expr,
                            SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) {
    aa->int_data.clear();
    aa->str_data.clear();
    return true;
  }
  if (aa->is_string_key) {
    aa->str_data.erase(EvalStrKey(expr->args[0], ctx, arena));
  } else {
    aa->int_data.erase(EvalIntKey(expr->args[0], ctx, arena));
  }
  return true;
}

bool TryExecAssocMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  auto* aa = ctx.FindAssocArray(parts.var_name);
  if (!aa) return false;
  if (parts.method_name == "delete")
    return ExecAssocDelete(aa, expr, ctx, arena);
  return false;
}

bool TryEvalAssocProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out) {
  auto* aa = ctx.FindAssocArray(var_name);
  if (!aa) return false;
  if (prop == "size" || prop == "num") {
    out = MakeLogic4VecVal(arena, 32, aa->Size());
    return true;
  }
  return false;
}

bool TryExecAssocPropertyStmt(std::string_view var_name, std::string_view prop,
                              SimContext& ctx, Arena& /*arena*/) {
  auto* aa = ctx.FindAssocArray(var_name);
  if (!aa) return false;
  if (prop == "delete") {
    aa->int_data.clear();
    aa->str_data.clear();
    return true;
  }
  return false;
}

// --- Locator methods (§7.12.1) ---

// Check if any element of an unpacked array is a string variable.
static bool IsStringArray(std::string_view var_name, const ArrayInfo& info,
                          SimContext& ctx) {
  if (info.is_dynamic) return ctx.IsStringVariable(var_name);
  auto name = std::string(var_name) + "[" + std::to_string(info.lo) + "]";
  return ctx.IsStringVariable(name);
}

// §7.12.1/§7.12.5: Check if a method name is a locator or map method.
static bool IsLocatorMethod(std::string_view name) {
  return name == "find" || name == "find_first" || name == "find_last" ||
         name == "find_index" || name == "find_last_index" ||
         name == "unique" || name == "unique_index" || name == "map";
}

// Bundles common locator method arguments to stay within 5-parameter limit.
struct LocatorCtx {
  const std::vector<Logic4Vec>& elems;
  bool is_string;
  const Expr* with_expr;
  SimContext& ctx;
  Arena& arena;
};

// Evaluate a with-clause predicate with 'item' bound to a value.
static bool EvalLocatorPredicate(const LocatorCtx& lc,
                                 const Logic4Vec& item_val, size_t item_index) {
  lc.ctx.PushScope();
  auto* item_var = lc.ctx.CreateLocalVariable("item", item_val.width);
  item_var->value = item_val;
  if (lc.is_string) lc.ctx.RegisterStringVariable("item");
  auto* idx_var = lc.ctx.CreateLocalVariable("item.index", 32);
  idx_var->value =
      MakeLogic4VecVal(lc.arena, 32, static_cast<uint64_t>(item_index));
  auto result = EvalExpr(lc.with_expr, lc.ctx, lc.arena).ToUint64();
  lc.ctx.PopScope();
  return result != 0;
}

// §7.12.1: find/find_first/find_last with predicate.
static void LocatorFind(std::string_view method, const LocatorCtx& lc,
                        std::vector<Logic4Vec>& out) {
  for (size_t i = 0; i < lc.elems.size(); ++i) {
    if (!EvalLocatorPredicate(lc, lc.elems[i], i)) continue;
    out.push_back(lc.elems[i]);
    if (method == "find_first" || method == "find_last") break;
  }
}

// §7.12.1: find/find_last — process in appropriate order.
static void LocatorFindDispatch(std::string_view method, const LocatorCtx& lc,
                                std::vector<Logic4Vec>& out) {
  if (method == "find_last") {
    for (size_t i = lc.elems.size(); i > 0; --i) {
      if (!EvalLocatorPredicate(lc, lc.elems[i - 1], i - 1)) continue;
      out.push_back(lc.elems[i - 1]);
      break;
    }
    return;
  }
  LocatorFind(method, lc, out);
}

// §7.12.1: find_index/find_last_index with predicate.
static void LocatorFindIndex(std::string_view method, const LocatorCtx& lc,
                             std::vector<Logic4Vec>& out) {
  if (method == "find_last_index") {
    for (size_t i = lc.elems.size(); i > 0; --i) {
      if (!EvalLocatorPredicate(lc, lc.elems[i - 1], i - 1)) continue;
      out.push_back(
          MakeLogic4VecVal(lc.arena, 32, static_cast<uint64_t>(i - 1)));
      break;
    }
    return;
  }
  for (size_t i = 0; i < lc.elems.size(); ++i) {
    if (!EvalLocatorPredicate(lc, lc.elems[i], i)) continue;
    out.push_back(MakeLogic4VecVal(lc.arena, 32, static_cast<uint64_t>(i)));
  }
}

// §7.12.5: map — transform each element via with-clause.
static void LocatorMap(const LocatorCtx& lc, std::vector<Logic4Vec>& out) {
  for (size_t i = 0; i < lc.elems.size(); ++i) {
    lc.ctx.PushScope();
    auto* item_var = lc.ctx.CreateLocalVariable("item", lc.elems[i].width);
    item_var->value = lc.elems[i];
    if (lc.is_string) lc.ctx.RegisterStringVariable("item");
    auto* idx_var = lc.ctx.CreateLocalVariable("item.index", 32);
    idx_var->value = MakeLogic4VecVal(lc.arena, 32, static_cast<uint64_t>(i));
    out.push_back(EvalExpr(lc.with_expr, lc.ctx, lc.arena));
    lc.ctx.PopScope();
  }
}

// §7.12.1: unique — return queue of distinct values.
static void LocatorUnique(const std::vector<Logic4Vec>& elems, Arena& /*arena*/,
                          std::vector<Logic4Vec>& out) {
  std::vector<uint64_t> seen;
  for (const auto& e : elems) {
    uint64_t v = e.ToUint64();
    bool dup = false;
    for (uint64_t s : seen) {
      if (s == v) {
        dup = true;
        break;
      }
    }
    if (!dup) {
      seen.push_back(v);
      out.push_back(e);
    }
  }
}

// §7.12.1: unique_index — return queue of indices of first occurrences.
static void LocatorUniqueIndex(const std::vector<Logic4Vec>& elems,
                               Arena& arena, std::vector<Logic4Vec>& out) {
  std::vector<uint64_t> seen;
  for (size_t i = 0; i < elems.size(); ++i) {
    uint64_t v = elems[i].ToUint64();
    bool dup = false;
    for (uint64_t s : seen) {
      if (s == v) {
        dup = true;
        break;
      }
    }
    if (!dup) {
      seen.push_back(v);
      out.push_back(MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(i)));
    }
  }
}

// Extract var and method names from member access (e.g., s.find, s.unique).
static bool ExtractLocatorParts(const Expr* expr, MethodCallParts& out) {
  // Member access pattern: s.find (no parens).
  if (expr->kind == ExprKind::kMemberAccess) {
    if (!expr->lhs || expr->lhs->kind != ExprKind::kIdentifier) return false;
    if (!expr->rhs || expr->rhs->kind != ExprKind::kIdentifier) return false;
    out.var_name = expr->lhs->text;
    out.method_name = expr->rhs->text;
    return true;
  }
  // Function call pattern: s.find() (with parens).
  return ExtractMethodCallParts(expr, out);
}

bool TryCollectLocatorResult(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::vector<Logic4Vec>& out) {
  MethodCallParts parts;
  if (!ExtractLocatorParts(expr, parts)) return false;
  if (!IsLocatorMethod(parts.method_name)) return false;

  auto* info = ctx.FindArrayInfo(parts.var_name);
  if (!info) return false;

  auto elems = CollectVecElements(parts.var_name, *info, ctx, arena);
  bool is_str = IsStringArray(parts.var_name, *info, ctx);

  if (parts.method_name == "unique") {
    LocatorUnique(elems, arena, out);
    return true;
  }
  if (parts.method_name == "unique_index") {
    LocatorUniqueIndex(elems, arena, out);
    return true;
  }

  // All other locator methods require a with clause.
  if (!expr->with_expr) return false;

  LocatorCtx lc{elems, is_str, expr->with_expr, ctx, arena};
  if (parts.method_name == "map") {
    LocatorMap(lc, out);
  } else if (parts.method_name == "find_index" ||
             parts.method_name == "find_last_index") {
    LocatorFindIndex(parts.method_name, lc, out);
  } else {
    LocatorFindDispatch(parts.method_name, lc, out);
  }
  return true;
}

}  // namespace delta
