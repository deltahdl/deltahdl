// §7.9: the associative array methods, and the key handling they need.
//
// §7.9.1 makes an associative array's index "an arbitrary expression of a
// singular type", so a key is either a string or an integral value and the
// methods split along that line all the way down. §7.9.2's num() and size(),
// §7.9.3's delete(), §7.9.4's exists(), and §7.9.5 through §7.9.8's first(),
// last(), next() and prev() -- the traversal methods, which write the key they
// reached back into the reference argument they were handed.
//
// These were in src/simulator/eval_array.cpp, which reached 973 lines against
// the 1000 assert-no-oversized-source-files in .github/workflows/deltahdl.yml
// fails at. What stays there is the fixed-size and dynamic array side: §7.12's
// reduction, ordering and locator methods, which reach their elements through
// ArrayInfo rather than through the key.
//
// The one name the two share is TryAssocReduction, declared in
// simulator/eval_array_internal.h: §7.12.3's reductions are defined over an
// associative array too, and both this file's method dispatch and its num()
// have to offer them before falling through to §7.9's own.

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

// The index-type spec of an associative array (§7.8): how an index expression
// is reduced to a stored key. Mirrors the AssocArrayObject index fields.
struct AssocKeySpec {
  uint32_t index_width = 64;
  bool is_wildcard = false;
  bool is_signed = true;
};

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

static std::string EvalStrKey(const Expr* expr, SimContext& ctx, Arena& arena) {
  return Vec2Str(EvalExpr(expr, ctx, arena));
}

static int64_t EvalIntKey(const Expr* expr, SimContext& ctx, Arena& arena,
                          const AssocKeySpec& spec = {}) {
  auto val = EvalExpr(expr, ctx, arena);
  if (HasUnknownBits(val)) {
    ctx.GetDiag().Warning(expr->range.start,
                          "associative array index contains x/z",
                          Subclause("7.8.6"));
  }
  return AssocIntKey(val, spec.is_wildcard, spec.index_width, spec.is_signed);
}

static bool AssocExists(AssocArrayObject* aa, const Expr* expr, SimContext& ctx,
                        Arena& arena, Logic4Vec& out) {
  if (expr->args.empty()) return false;
  uint64_t found = 0;
  if (aa->is_string_key) {
    found = aa->str_data.count(EvalStrKey(expr->args[0], ctx, arena)) ? 1 : 0;
  } else {
    found = aa->int_data.count(EvalIntKey(
                expr->args[0], ctx, arena,
                {aa->index_width, aa->is_wildcard, aa->is_index_signed}))
                ? 1
                : 0;
  }
  out = MakeLogic4VecVal(arena, 32, found);
  return true;
}

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
  if (method == "next") {
    // §7.9.6 — next() yields the smallest index strictly greater than the
    // argument value. The argument need not itself be a stored index, so
    // compare by value rather than locating an existing entry first.
    auto it = m.upper_bound(cur_key);
    if (it == m.end()) {
      out = MakeLogic4VecVal(arena, 32, 0);
      return true;
    }
    ref_var->value = Str2Vec(it->first, arena);
    out = MakeLogic4VecVal(arena, 32, 1);
    return true;
  }
  // §7.9.7 — prev() yields the largest index strictly smaller than the
  // argument value. The argument need not itself be a stored index, so locate
  // the lower bound by value and step back to its predecessor.
  auto it = m.lower_bound(cur_key);
  if (it == m.begin()) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }
  --it;
  ref_var->value = Str2Vec(it->first, arena);
  out = MakeLogic4VecVal(arena, 32, 1);
  return true;
}

static int WriteTraversalKey(Variable* ref, int64_t key, uint32_t idx_width,
                             Arena& arena) {
  uint32_t w = ref->value.width;
  if (w == 0) w = 32;
  ref->value = MakeLogic4VecVal(arena, w, static_cast<uint64_t>(key));
  return (w < idx_width) ? -1 : 1;
}

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
  if (method == "next") {
    // §7.9.6 — next() yields the smallest index strictly greater than the
    // argument value. The argument need not itself be a stored index, so
    // compare by value rather than locating an existing entry first.
    auto it = m.upper_bound(cur_key);
    if (it == m.end()) {
      out = MakeLogic4VecVal(arena, 32, 0);
      return true;
    }
    auto r = WriteTraversalKey(ref_var, it->first, aa->index_width, arena);
    out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(r));
    return true;
  }
  // §7.9.7 — prev() yields the largest index strictly smaller than the
  // argument value. The argument need not itself be a stored index, so locate
  // the lower bound by value and step back to its predecessor.
  auto it = m.lower_bound(cur_key);
  if (it == m.begin()) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }
  --it;
  auto r = WriteTraversalKey(ref_var, it->first, aa->index_width, arena);
  out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(r));
  return true;
}

std::vector<Logic4Vec> AssocIndexValues(const AssocArrayObject* aa,
                                        Arena& arena) {
  std::vector<Logic4Vec> keys;
  if (aa->is_string_key) {
    keys.reserve(aa->str_data.size());
    for (const auto& [key, val] : aa->str_data)
      keys.push_back(Str2Vec(key, arena));
    return keys;
  }
  keys.reserve(aa->int_data.size());
  uint32_t width = aa->index_width == 0 ? 32 : aa->index_width;
  for (const auto& [key, val] : aa->int_data) {
    Logic4Vec index =
        MakeLogic4VecVal(arena, width, static_cast<uint64_t>(key));
    index.is_signed = aa->is_index_signed;
    keys.push_back(index);
  }
  return keys;
}

static Variable* ResolveTraversalRef(const Expr* expr, SimContext& ctx) {
  if (expr->args.empty()) return nullptr;
  auto* ref_expr = expr->args[0];
  if (ref_expr->kind != ExprKind::kIdentifier) return nullptr;
  return ctx.FindVariable(ref_expr->text);
}

static bool AssocTraversal(AssocArrayObject* aa, std::string_view method,
                           Variable* ref_var, Arena& arena, Logic4Vec& out) {
  if (aa->is_string_key)
    return AssocStrTraversal(aa, method, ref_var, arena, out);
  return AssocIntTraversal(aa, method, ref_var, arena, out);
}

// The associative array the call `receiver.method(...)` is on, and the method,
// or null for a call of another shape or on a receiver that names no
// associative array. §7.9's methods are defined on the array whatever names
// it: a declared array by its bare name, and, §8.5 putting no restriction on
// a property's type, a property of an object -- the running method's own by
// its bare name (§8.11) or any object's through a handle, `o.count.size()` --
// which FindAssocArrayOfBase resolves. Before it, only the bare name of a
// declared array was read here, so `m_severity_count.size()` in a method of
// UVM's uvm_report_server declined and read 0.
static AssocArrayObject* CallReceiverAssoc(const Expr* expr,
                                           std::string_view& method,
                                           SimContext& ctx, Arena& arena) {
  if (expr == nullptr || expr->lhs == nullptr ||
      expr->lhs->kind != ExprKind::kMemberAccess) {
    return nullptr;
  }
  const Expr* access = expr->lhs;
  if (access->is_scope_resolution || access->lhs == nullptr ||
      access->rhs == nullptr || access->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  method = access->rhs->text;
  return FindAssocArrayOfBase(access->lhs, ctx, arena);
}

bool TryEvalAssocMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out) {
  std::string_view method;
  auto* aa = CallReceiverAssoc(expr, method, ctx, arena);
  if (!aa) return false;
  if (method == "size" || method == "num") {
    out = MakeLogic4VecVal(arena, 32, aa->Size());
    return true;
  }
  if (method == "exists") return AssocExists(aa, expr, ctx, arena, out);
  if (method == "delete") {
    TryExecAssocMethodStmt(expr, ctx, arena);
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (method == "first" || method == "last" || method == "next" ||
      method == "prev") {
    auto* ref_var = ResolveTraversalRef(expr, ctx);
    if (!ref_var) {
      out = MakeLogic4VecVal(arena, 32, 0);
      return true;
    }
    return AssocTraversal(aa, method, ref_var, arena, out);
  }
  if (auto reduced = TryAssocReduction(aa, method, expr, ctx, arena)) {
    out = *reduced;
    return true;
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
    aa->int_data.erase(
        EvalIntKey(expr->args[0], ctx, arena,
                   {aa->index_width, aa->is_wildcard, aa->is_index_signed}));
  }
  return true;
}

bool TryExecAssocMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena) {
  std::string_view method;
  auto* aa = CallReceiverAssoc(expr, method, ctx, arena);
  if (!aa) return false;
  if (method == "delete") return ExecAssocDelete(aa, expr, ctx, arena);
  return false;
}

// §7.9.1 writes `imem.num` without parentheses, and the name on the left of
// the dot is read as a call's receiver is: a declared array, or the property
// of the running method's object (§8.11).
bool TryEvalAssocProperty(std::string_view var_name, std::string_view prop,
                          SimContext& ctx, Arena& arena, Logic4Vec& out) {
  auto* aa = FindAssocArrayOfName(var_name, ctx);
  if (!aa) return false;
  if (prop == "size" || prop == "num") {
    out = MakeLogic4VecVal(arena, 32, aa->Size());
    return true;
  }
  if (auto reduced = TryAssocReduction(aa, prop, nullptr, ctx, arena)) {
    out = *reduced;
    return true;
  }
  return false;
}

bool TryExecAssocPropertyStmt(std::string_view var_name, std::string_view prop,
                              SimContext& ctx, Arena&) {
  auto* aa = FindAssocArrayOfName(var_name, ctx);
  if (!aa) return false;
  if (prop == "delete") {
    aa->int_data.clear();
    aa->str_data.clear();
    return true;
  }
  return false;
}
}  // namespace delta
