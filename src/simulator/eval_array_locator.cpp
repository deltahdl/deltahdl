#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

static bool IsStringArray(std::string_view var_name, const ArrayInfo& info,
                          SimContext& ctx) {
  if (info.is_dynamic) return ctx.IsStringVariable(var_name);
  auto name = std::string(var_name) + "[" + std::to_string(info.lo) + "]";
  return ctx.IsStringVariable(name);
}

static bool IsLocatorMethod(std::string_view name) {
  return name == "find" || name == "find_first" || name == "find_last" ||
         name == "find_index" || name == "find_first_index" ||
         name == "find_last_index" || name == "min" || name == "max" ||
         name == "unique" || name == "unique_index" || name == "map";
}

struct LocatorCtx {
  const std::vector<Logic4Vec>& elems;
  bool is_string;
  const Expr* with_expr;
  SimContext& ctx;
  Arena& arena;
  std::string_view iter_name = "item";
  std::string idx_var_name = "item.index";
};

static LocatorCtx MakeLocatorCtx(const std::vector<Logic4Vec>& elems,
                                 bool is_str, const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  auto names = ExtractIterNames(expr);
  return LocatorCtx{elems,
                    is_str,
                    expr->with_expr,
                    ctx,
                    arena,
                    names.iter_name,
                    std::move(names.idx_var_name)};
}

// Pushes a fresh scope and binds the per-iteration locator iterators: the
// element iterator (item_val, optionally registered as a string) and the index
// iterator (item_index, 32-bit). The caller is responsible for evaluating the
// with expression in this scope and calling PopScope afterwards.
static void SetupLocatorScope(const LocatorCtx& lc, const Logic4Vec& item_val,
                              size_t item_index) {
  lc.ctx.PushScope();
  auto* item_var = lc.ctx.CreateLocalVariable(lc.iter_name, item_val.width);
  item_var->value = item_val;
  if (lc.is_string) lc.ctx.RegisterStringVariable(lc.iter_name);
  auto* idx_var = lc.ctx.CreateLocalVariable(lc.idx_var_name, 32);
  idx_var->value =
      MakeLogic4VecVal(lc.arena, 32, static_cast<uint64_t>(item_index));
}

static bool EvalLocatorPredicate(const LocatorCtx& lc,
                                 const Logic4Vec& item_val, size_t item_index) {
  SetupLocatorScope(lc, item_val, item_index);
  auto result = EvalExpr(lc.with_expr, lc.ctx, lc.arena).ToUint64();
  lc.ctx.PopScope();
  return result != 0;
}

static Logic4Vec EvalLocatorWithExpr(const LocatorCtx& lc,
                                     const Logic4Vec& item_val,
                                     size_t item_index) {
  SetupLocatorScope(lc, item_val, item_index);
  auto result = EvalExpr(lc.with_expr, lc.ctx, lc.arena);
  lc.ctx.PopScope();
  return result;
}

static void LocatorFind(std::string_view method, const LocatorCtx& lc,
                        std::vector<Logic4Vec>& out) {
  for (size_t i = 0; i < lc.elems.size(); ++i) {
    if (!EvalLocatorPredicate(lc, lc.elems[i], i)) continue;
    out.push_back(lc.elems[i]);
    if (method == "find_first" || method == "find_last") break;
  }
}

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
    if (method == "find_first_index") break;
  }
}

static void LocatorMap(const LocatorCtx& lc, std::vector<Logic4Vec>& out) {
  for (size_t i = 0; i < lc.elems.size(); ++i) {
    lc.ctx.PushScope();
    auto* item_var =
        lc.ctx.CreateLocalVariable(lc.iter_name, lc.elems[i].width);
    item_var->value = lc.elems[i];
    if (lc.is_string) lc.ctx.RegisterStringVariable(lc.iter_name);
    auto* idx_var = lc.ctx.CreateLocalVariable(lc.idx_var_name, 32);
    idx_var->value = MakeLogic4VecVal(lc.arena, 32, static_cast<uint64_t>(i));
    out.push_back(EvalExpr(lc.with_expr, lc.ctx, lc.arena));
    lc.ctx.PopScope();
  }
}

static void LocatorUnique(const std::vector<Logic4Vec>& elems, Arena&,
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

static void LocatorMinMax(std::string_view method, const LocatorCtx& lc,
                          std::vector<Logic4Vec>& out) {
  if (lc.elems.empty()) return;
  size_t best_idx = 0;
  uint64_t best_val = lc.with_expr
                          ? EvalLocatorWithExpr(lc, lc.elems[0], 0).ToUint64()
                          : lc.elems[0].ToUint64();
  for (size_t i = 1; i < lc.elems.size(); ++i) {
    uint64_t val = lc.with_expr
                       ? EvalLocatorWithExpr(lc, lc.elems[i], i).ToUint64()
                       : lc.elems[i].ToUint64();
    if ((method == "min" && val < best_val) ||
        (method == "max" && val > best_val)) {
      best_val = val;
      best_idx = i;
    }
  }
  out.push_back(lc.elems[best_idx]);
}

// De-duplicates by the value of the with expression. For each first-seen
// distinct with-value, pushes either the matching element (use_index=false) or
// its 0-based position as a 32-bit value (use_index=true).
static void DedupeLocatorResults(const LocatorCtx& lc, bool use_index,
                                 std::vector<Logic4Vec>& out) {
  std::vector<uint64_t> seen;
  for (size_t i = 0; i < lc.elems.size(); ++i) {
    uint64_t v = EvalLocatorWithExpr(lc, lc.elems[i], i).ToUint64();
    bool dup = false;
    for (uint64_t s : seen) {
      if (s == v) {
        dup = true;
        break;
      }
    }
    if (!dup) {
      seen.push_back(v);
      out.push_back(
          use_index ? MakeLogic4VecVal(lc.arena, 32, static_cast<uint64_t>(i))
                    : lc.elems[i]);
    }
  }
}

static void LocatorUniqueWith(const LocatorCtx& lc,
                              std::vector<Logic4Vec>& out) {
  DedupeLocatorResults(lc, /*use_index=*/false, out);
}

static void LocatorUniqueIndexWith(const LocatorCtx& lc,
                                   std::vector<Logic4Vec>& out) {
  DedupeLocatorResults(lc, /*use_index=*/true, out);
}

static bool ExtractLocatorParts(const Expr* expr, MethodCallParts& out) {
  if (expr->kind == ExprKind::kMemberAccess) {
    if (!expr->lhs || expr->lhs->kind != ExprKind::kIdentifier) return false;
    if (!expr->rhs || expr->rhs->kind != ExprKind::kIdentifier) return false;
    out.var_name = expr->lhs->text;
    out.method_name = expr->rhs->text;
    return true;
  }

  return ExtractMethodCallParts(expr, out);
}

// §7.12.1 — array locator methods over an associative array. Two rules differ
// from the indexed-array case: index locators (find_index/.../unique_index)
// return a queue of the *index type* holding the matching keys rather than a
// queue of int holding 0-based positions; and "first"/"last" are the entries
// with the smallest/largest index (the first()/last() ordering of 7.9), which a
// std::map gives for free by visiting keys in ascending order. Only integer
// keys are representable through this value vector — string-keyed and wildcard
// arrays are left for the caller to handle.
static bool TryCollectAssocLocatorResult(const Expr* expr,
                                         const MethodCallParts& parts,
                                         AssocArrayObject& aa, SimContext& ctx,
                                         Arena& arena,
                                         std::vector<Logic4Vec>& out) {
  std::string_view method = parts.method_name;
  if (method == "map") return false;  // not a 7.12.1 locator method

  const bool kNeedsWith = method == "find" || method == "find_index" ||
                          method == "find_first" ||
                          method == "find_first_index" ||
                          method == "find_last" || method == "find_last_index";
  if (!expr->with_expr && kNeedsWith) {
    ctx.GetDiag().Error({}, "array locator method '" + std::string(method) +
                                "' requires a 'with' clause");
    return false;
  }
  if (aa.is_string_key) return false;  // index type not representable here

  std::vector<int64_t> keys;
  std::vector<Logic4Vec> vals;
  for (const auto& [k, v] : aa.int_data) {
    keys.push_back(k);
    vals.push_back(v);
  }

  LocatorCtx lc = MakeLocatorCtx(vals, /*is_str=*/false, expr, ctx, arena);
  const uint32_t kIw = aa.index_width;
  auto key_vec = [&](size_t i) {
    return MakeLogic4VecVal(arena, kIw, static_cast<uint64_t>(keys[i]));
  };
  // Evaluates the with expression for entry i, binding the element iterator to
  // the value and the index iterator to the key.
  auto eval_with = [&](size_t i) {
    ctx.PushScope();
    auto* item_var = ctx.CreateLocalVariable(lc.iter_name, vals[i].width);
    item_var->value = vals[i];
    auto* idx_var = ctx.CreateLocalVariable(lc.idx_var_name, kIw);
    idx_var->value = key_vec(i);
    Logic4Vec r = EvalExpr(lc.with_expr, ctx, arena);
    ctx.PopScope();
    return r;
  };
  auto matches = [&](size_t i) { return eval_with(i).ToUint64() != 0; };
  auto sort_key = [&](size_t i) {
    return lc.with_expr ? eval_with(i).ToUint64() : vals[i].ToUint64();
  };

  if (method == "find") {
    for (size_t i = 0; i < vals.size(); ++i)
      if (matches(i)) out.push_back(vals[i]);
  } else if (method == "find_first") {
    for (size_t i = 0; i < vals.size(); ++i)
      if (matches(i)) {
        out.push_back(vals[i]);
        break;
      }
  } else if (method == "find_last") {
    for (size_t i = vals.size(); i > 0; --i)
      if (matches(i - 1)) {
        out.push_back(vals[i - 1]);
        break;
      }
  } else if (method == "find_index") {
    for (size_t i = 0; i < vals.size(); ++i)
      if (matches(i)) out.push_back(key_vec(i));
  } else if (method == "find_first_index") {
    for (size_t i = 0; i < vals.size(); ++i)
      if (matches(i)) {
        out.push_back(key_vec(i));
        break;
      }
  } else if (method == "find_last_index") {
    for (size_t i = vals.size(); i > 0; --i)
      if (matches(i - 1)) {
        out.push_back(key_vec(i - 1));
        break;
      }
  } else if (method == "min" || method == "max") {
    if (vals.empty()) return true;
    size_t best = 0;
    uint64_t best_key = sort_key(0);
    for (size_t i = 1; i < vals.size(); ++i) {
      uint64_t k = sort_key(i);
      if ((method == "min" && k < best_key) ||
          (method == "max" && k > best_key)) {
        best_key = k;
        best = i;
      }
    }
    out.push_back(vals[best]);
  } else if (method == "unique" || method == "unique_index") {
    std::vector<uint64_t> seen;
    for (size_t i = 0; i < vals.size(); ++i) {
      uint64_t v = sort_key(i);
      bool dup = false;
      for (uint64_t s : seen)
        if (s == v) {
          dup = true;
          break;
        }
      if (dup) continue;
      seen.push_back(v);
      out.push_back(method == "unique" ? vals[i] : key_vec(i));
    }
  } else {
    return false;
  }
  return true;
}

bool TryCollectLocatorResult(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::vector<Logic4Vec>& out) {
  MethodCallParts parts;
  if (!ExtractLocatorParts(expr, parts)) return false;
  if (!IsLocatorMethod(parts.method_name)) return false;

  if (!expr->args.empty() && !expr->with_expr) {
    ctx.GetDiag().Error({}, "iterator argument without 'with' clause");
    return false;
  }

  auto* info = ctx.FindArrayInfo(parts.var_name);
  if (!info) {
    // Associative arrays are stored separately and honor index-type returns
    // and key ordering through a dedicated path.
    if (auto* aa = ctx.FindAssocArray(parts.var_name))
      return TryCollectAssocLocatorResult(expr, parts, *aa, ctx, arena, out);
    return false;
  }

  auto elems = CollectVecElements(parts.var_name, *info, ctx, arena);
  bool is_str = IsStringArray(parts.var_name, *info, ctx);

  if (parts.method_name == "unique") {
    if (expr->with_expr) {
      LocatorCtx lc = MakeLocatorCtx(elems, is_str, expr, ctx, arena);
      LocatorUniqueWith(lc, out);
    } else {
      LocatorUnique(elems, arena, out);
    }
    return true;
  }
  if (parts.method_name == "unique_index") {
    if (expr->with_expr) {
      LocatorCtx lc = MakeLocatorCtx(elems, is_str, expr, ctx, arena);
      LocatorUniqueIndexWith(lc, out);
    } else {
      LocatorUniqueIndex(elems, arena, out);
    }
    return true;
  }
  if (parts.method_name == "min" || parts.method_name == "max") {
    LocatorCtx lc = MakeLocatorCtx(elems, is_str, expr, ctx, arena);
    LocatorMinMax(parts.method_name, lc, out);
    return true;
  }

  // §7.12.5 — map() replaces each element with the value of its with clause,
  // and that clause is required: there is nothing to evaluate without it, so a
  // bare map() is illegal rather than a silent no-op.
  if (parts.method_name == "map" && !expr->with_expr) {
    ctx.GetDiag().Error({}, "array method 'map' requires a 'with' clause");
    return false;
  }

  if (!expr->with_expr) {
    // §7.12.1 — the with clause is mandatory for the element- and
    // index-finding locators; it carries the Boolean predicate they filter on.
    // A bare find* call is illegal, so flag it instead of silently yielding
    // nothing.
    if (parts.method_name == "find" || parts.method_name == "find_index" ||
        parts.method_name == "find_first" ||
        parts.method_name == "find_first_index" ||
        parts.method_name == "find_last" ||
        parts.method_name == "find_last_index") {
      ctx.GetDiag().Error({}, "array locator method '" +
                                  std::string(parts.method_name) +
                                  "' requires a 'with' clause");
    }
    return false;
  }

  LocatorCtx lc = MakeLocatorCtx(elems, is_str, expr, ctx, arena);
  if (parts.method_name == "map") {
    LocatorMap(lc, out);
  } else if (parts.method_name == "find_index" ||
             parts.method_name == "find_first_index" ||
             parts.method_name == "find_last_index") {
    LocatorFindIndex(parts.method_name, lc, out);
  } else {
    LocatorFindDispatch(parts.method_name, lc, out);
  }
  return true;
}

// §7.12.5 — map() over an associative array. Unlike the locator methods, map
// does not collapse the array to a queue: it produces an associative array
// whose set of index values and index type match the source, with each stored
// value replaced by the value of the with expression. The with clause is
// required, and each result element takes the self-determined type of that
// expression (carried by the width of the evaluated value). Only the
// integer-keyed index type is representable through this path; string-keyed
// sources are left to the caller, mirroring the locator-result limitation.
bool TryCollectAssocMapResult(const Expr* expr, SimContext& ctx, Arena& arena,
                              AssocArrayObject& out) {
  MethodCallParts parts;
  if (!ExtractLocatorParts(expr, parts)) return false;
  if (parts.method_name != "map") return false;
  auto* aa = ctx.FindAssocArray(parts.var_name);
  if (!aa) return false;
  if (!expr->with_expr) {
    ctx.GetDiag().Error({}, "array method 'map' requires a 'with' clause");
    return false;
  }
  if (aa->is_string_key) return false;  // index type not representable here

  // The returned array's range and index type match the source: carry over the
  // index metadata and reuse the source keys unchanged.
  out.index_width = aa->index_width;
  out.is_index_signed = aa->is_index_signed;
  out.is_wildcard = aa->is_wildcard;
  out.is_string_key = false;
  out.int_data.clear();

  std::vector<int64_t> keys;
  std::vector<Logic4Vec> vals;
  for (const auto& [k, v] : aa->int_data) {
    keys.push_back(k);
    vals.push_back(v);
  }
  LocatorCtx lc = MakeLocatorCtx(vals, /*is_str=*/false, expr, ctx, arena);
  const uint32_t kIw = aa->index_width;
  for (size_t i = 0; i < vals.size(); ++i) {
    ctx.PushScope();
    auto* item_var = ctx.CreateLocalVariable(lc.iter_name, vals[i].width);
    item_var->value = vals[i];
    auto* idx_var = ctx.CreateLocalVariable(lc.idx_var_name, kIw);
    idx_var->value =
        MakeLogic4VecVal(arena, kIw, static_cast<uint64_t>(keys[i]));
    Logic4Vec mapped = EvalExpr(lc.with_expr, ctx, arena);
    ctx.PopScope();
    out.int_data[keys[i]] = mapped;
    out.elem_width = mapped.width;
  }
  return true;
}

}  // namespace delta
