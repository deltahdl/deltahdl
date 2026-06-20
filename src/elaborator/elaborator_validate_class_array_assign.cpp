#include <cstdint>
#include <format>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

void Elaborator::CheckArrayAssignExprs(const Expr* lhs, const Expr* rhs,
                                       SourceLoc loc) {
  if (!lhs || !rhs) return;
  if (lhs->kind != ExprKind::kIdentifier) return;
  if (rhs->kind != ExprKind::kIdentifier) return;
  auto lhs_it = var_array_info_.find(lhs->text);
  auto rhs_it = var_array_info_.find(rhs->text);
  if (lhs_it == var_array_info_.end() || rhs_it == var_array_info_.end()) {
    if (lhs_it != var_array_info_.end() &&
        packed_array_vars_.count(rhs->text)) {
      diag_.Error(loc,
                  std::format("packed array '{}' cannot be directly assigned "
                              "to unpacked array '{}' without an explicit cast",
                              rhs->text, lhs->text));
    }
    return;
  }
  const auto& l = lhs_it->second;
  const auto& r = rhs_it->second;

  if (l.is_assoc != r.is_assoc) {
    diag_.Error(loc,
                "associative array cannot be assigned to or from a "
                "non-associative array");
    return;
  }
  if (l.is_assoc && r.is_assoc && l.assoc_index_type != r.assoc_index_type) {
    diag_.Error(loc, "associative array index type mismatch in assignment");
    return;
  }

  if (l.num_unpacked_dims != r.num_unpacked_dims) {
    diag_.Error(loc,
                std::format("array assignment requires the same number of "
                            "unpacked dimensions ('{}' has {}, '{}' has {})",
                            lhs->text, l.num_unpacked_dims, rhs->text,
                            r.num_unpacked_dims));
    return;
  }

  if (!ElementTypesEquivalent(l.elem_type, l.elem_width, l.elem_is_signed,
                              l.elem_is_4state, r.elem_type, r.elem_width,
                              r.elem_is_signed, r.elem_is_4state)) {
    diag_.Error(loc, std::format("array element type mismatch in assignment "
                                 "('{}' vs '{}')",
                                 lhs->text, rhs->text));
    return;
  }
  if (l.unpacked_size > 0 && !l.is_dynamic && r.unpacked_size > 0 &&
      !r.is_dynamic && l.unpacked_size != r.unpacked_size) {
    diag_.Error(
        loc,
        std::format("array size mismatch: '{}' has {} elements but "
                    "'{}' has {}",
                    lhs->text, l.unpacked_size, rhs->text, r.unpacked_size));
    return;
  }

  if (!l.is_dynamic && !r.is_dynamic && !l.is_assoc && !r.is_assoc &&
      l.dim_sizes.size() == r.dim_sizes.size() && l.dim_sizes.size() > 1) {
    for (size_t i = 1; i < l.dim_sizes.size(); ++i) {
      if (l.dim_sizes[i] != r.dim_sizes[i]) {
        diag_.Error(
            loc,
            std::format("faster-varying array dimension size mismatch in "
                        "assignment ('{}' dim {} is {}, '{}' dim {} is {})",
                        lhs->text, i, l.dim_sizes[i], rhs->text, i,
                        r.dim_sizes[i]));
        return;
      }
    }
  }
}

void Elaborator::ValidateOneArrayAssignment(const ModuleItem* item) {
  if (!item->assign_lhs || !item->assign_rhs) return;
  CheckArrayAssignExprs(item->assign_lhs, item->assign_rhs, item->loc);
}

void Elaborator::WalkStmtsForArrayAssign(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckArrayAssignExprs(s->lhs, s->rhs, s->range.start);
  }
  for (auto* sub : s->stmts) WalkStmtsForArrayAssign(sub);
  WalkStmtsForArrayAssign(s->then_branch);
  WalkStmtsForArrayAssign(s->else_branch);
  WalkStmtsForArrayAssign(s->body);
  WalkStmtsForArrayAssign(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForArrayAssign(ci.body);
}

void Elaborator::ValidateArrayAssignments(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      ValidateOneArrayAssignment(item);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForArrayAssign(item->body);
    }
  }
}

static Elaborator::VarArrayInfo FormalArrayInfo(
    const FunctionArg& arg,
    const std::unordered_set<std::string_view>& class_names,
    const TypedefMap& typedefs) {
  Elaborator::VarArrayInfo info;
  info.elem_type = arg.data_type.kind;
  info.elem_width = EvalTypeWidth(arg.data_type, typedefs);
  info.elem_is_signed = arg.data_type.is_signed;
  info.elem_is_4state = Is4stateType(arg.data_type, typedefs);
  if (arg.unpacked_dims.empty()) return info;
  auto* dim = arg.unpacked_dims[0];
  if (!dim) {
    info.is_dynamic = true;
    return info;
  }
  if (dim->kind == ExprKind::kIdentifier) {
    auto t = dim->text;
    if (t == "$") return info;
    if (t == "string" || t == "int" || t == "integer" || t == "byte" ||
        t == "shortint" || t == "longint" || t == "*") {
      info.is_assoc = true;
      info.assoc_index_type = t;
      return info;
    }
    if (class_names.count(t) > 0) {
      info.is_assoc = true;
      info.assoc_index_type = t;
      return info;
    }
  }

  info.unpacked_size = 1;
  return info;
}

static void CheckArrayArgTypes(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const std::unordered_set<std::string_view>& class_names,
    const TypedefMap& typedefs, DiagEngine& diag) {
  if (!expr || expr->kind != ExprKind::kCall || expr->callee.empty()) return;
  auto it = func_decls.find(expr->callee);
  if (it == func_decls.end()) return;
  const auto* func = it->second;
  size_t positional_count = expr->args.size() - expr->arg_names.size();
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    const auto& formal = func->func_args[i];
    auto formal_info = FormalArrayInfo(formal, class_names, typedefs);

    if (formal.unpacked_dims.empty()) continue;

    int ai = -1;
    if (expr->arg_names.empty()) {
      ai = (i < expr->args.size()) ? static_cast<int>(i) : -1;
    } else if (i < positional_count) {
      ai = static_cast<int>(i);
    } else {
      for (size_t j = 0; j < expr->arg_names.size(); ++j) {
        if (expr->arg_names[j] == formal.name) {
          ai = static_cast<int>(positional_count + j);
          break;
        }
      }
    }
    if (ai < 0) continue;
    auto* actual = expr->args[static_cast<size_t>(ai)];
    if (!actual || actual->kind != ExprKind::kIdentifier) continue;
    auto ait = var_array_info.find(actual->text);
    if (ait == var_array_info.end()) continue;
    const auto& actual_info = ait->second;
    if (actual_info.is_assoc != formal_info.is_assoc) {
      diag.Error(actual->range.start,
                 "associative array cannot be passed to or from a "
                 "non-associative array parameter");
      continue;
    }
    if (actual_info.is_assoc && formal_info.is_assoc &&
        actual_info.assoc_index_type != formal_info.assoc_index_type) {
      diag.Error(actual->range.start,
                 "associative array index type mismatch in argument");
      continue;
    }
    // The value type carried by an associative actual must be equivalent to the
    // value type of the associative formal it binds to.
    if (actual_info.is_assoc && formal_info.is_assoc &&
        !ElementTypesEquivalent(
            actual_info.elem_type, actual_info.elem_width,
            actual_info.elem_is_signed, actual_info.elem_is_4state,
            formal_info.elem_type, formal_info.elem_width,
            formal_info.elem_is_signed, formal_info.elem_is_4state)) {
      diag.Error(actual->range.start,
                 "associative array element type mismatch in argument");
      continue;
    }
  }
}

static void WalkExprForArrayArgTypes(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const std::unordered_set<std::string_view>& class_names,
    const TypedefMap& typedefs, DiagEngine& diag) {
  if (!expr) return;
  CheckArrayArgTypes(expr, func_decls, var_array_info, class_names, typedefs,
                     diag);
  WalkExprForArrayArgTypes(expr->lhs, func_decls, var_array_info, class_names,
                           typedefs, diag);
  WalkExprForArrayArgTypes(expr->rhs, func_decls, var_array_info, class_names,
                           typedefs, diag);
  WalkExprForArrayArgTypes(expr->condition, func_decls, var_array_info,
                           class_names, typedefs, diag);
  WalkExprForArrayArgTypes(expr->true_expr, func_decls, var_array_info,
                           class_names, typedefs, diag);
  WalkExprForArrayArgTypes(expr->false_expr, func_decls, var_array_info,
                           class_names, typedefs, diag);
  for (auto* a : expr->args)
    WalkExprForArrayArgTypes(a, func_decls, var_array_info, class_names,
                             typedefs, diag);
  for (auto* e : expr->elements)
    WalkExprForArrayArgTypes(e, func_decls, var_array_info, class_names,
                             typedefs, diag);
}

static void WalkStmtForArrayArgTypes(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const std::unordered_set<std::string_view>& class_names,
    const TypedefMap& typedefs, DiagEngine& diag) {
  if (!s) return;
  WalkExprForArrayArgTypes(s->expr, func_decls, var_array_info, class_names,
                           typedefs, diag);
  WalkExprForArrayArgTypes(s->lhs, func_decls, var_array_info, class_names,
                           typedefs, diag);
  WalkExprForArrayArgTypes(s->rhs, func_decls, var_array_info, class_names,
                           typedefs, diag);
  WalkExprForArrayArgTypes(s->condition, func_decls, var_array_info,
                           class_names, typedefs, diag);
  for (auto* sub : s->stmts)
    WalkStmtForArrayArgTypes(sub, func_decls, var_array_info, class_names,
                             typedefs, diag);
  WalkStmtForArrayArgTypes(s->then_branch, func_decls, var_array_info,
                           class_names, typedefs, diag);
  WalkStmtForArrayArgTypes(s->else_branch, func_decls, var_array_info,
                           class_names, typedefs, diag);
  WalkStmtForArrayArgTypes(s->body, func_decls, var_array_info, class_names,
                           typedefs, diag);
  for (auto* fi : s->for_inits)
    WalkStmtForArrayArgTypes(fi, func_decls, var_array_info, class_names,
                             typedefs, diag);
  WalkStmtForArrayArgTypes(s->for_body, func_decls, var_array_info, class_names,
                           typedefs, diag);
  for (auto* fs : s->for_steps)
    WalkStmtForArrayArgTypes(fs, func_decls, var_array_info, class_names,
                             typedefs, diag);
  WalkExprForArrayArgTypes(s->for_cond, func_decls, var_array_info, class_names,
                           typedefs, diag);
  for (auto& ci : s->case_items)
    WalkStmtForArrayArgTypes(ci.body, func_decls, var_array_info, class_names,
                             typedefs, diag);
}

void Elaborator::ValidateArrayArgTypes(const ModuleDecl* decl) {
  std::unordered_map<std::string_view, const ModuleItem*> all_decls =
      func_decls_;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl) all_decls[item->name] = item;
  }
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kFinalBlock) {
      WalkStmtForArrayArgTypes(item->body, all_decls, var_array_info_,
                               class_names_, typedefs_, diag_);
    }
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      for (auto* s : item->func_body_stmts) {
        WalkStmtForArrayArgTypes(s, all_decls, var_array_info_, class_names_,
                                 typedefs_, diag_);
      }
    }
  }
}

bool IsSliceSelect(const Expr* e) {
  if (!e || e->kind != ExprKind::kSelect) return false;
  return e->is_part_select_plus || e->is_part_select_minus || e->index_end;
}

static void CheckAssocSliceExpr(
    const Expr* e, const std::unordered_set<std::string_view>& assoc_names,
    DiagEngine& diag) {
  if (!e) return;
  if (IsSliceSelect(e) && e->base && e->base->kind == ExprKind::kIdentifier) {
    if (assoc_names.count(e->base->text)) {
      diag.Error(e->range.start,
                 "slice is not allowed on an associative array");
    }
  }
  CheckAssocSliceExpr(e->lhs, assoc_names, diag);
  CheckAssocSliceExpr(e->rhs, assoc_names, diag);
  CheckAssocSliceExpr(e->base, assoc_names, diag);
  CheckAssocSliceExpr(e->index, assoc_names, diag);
  CheckAssocSliceExpr(e->index_end, assoc_names, diag);
  CheckAssocSliceExpr(e->condition, assoc_names, diag);
  CheckAssocSliceExpr(e->true_expr, assoc_names, diag);
  CheckAssocSliceExpr(e->false_expr, assoc_names, diag);
  for (const auto* elem : e->elements) {
    CheckAssocSliceExpr(elem, assoc_names, diag);
  }
}

static void WalkStmtsForAssocSlice(
    const Stmt* s, const std::unordered_set<std::string_view>& assoc_names,
    DiagEngine& diag) {
  if (!s) return;
  CheckAssocSliceExpr(s->lhs, assoc_names, diag);
  CheckAssocSliceExpr(s->rhs, assoc_names, diag);
  CheckAssocSliceExpr(s->expr, assoc_names, diag);
  CheckAssocSliceExpr(s->condition, assoc_names, diag);
  for (auto* sub : s->stmts) WalkStmtsForAssocSlice(sub, assoc_names, diag);
  WalkStmtsForAssocSlice(s->then_branch, assoc_names, diag);
  WalkStmtsForAssocSlice(s->else_branch, assoc_names, diag);
  WalkStmtsForAssocSlice(s->body, assoc_names, diag);
  WalkStmtsForAssocSlice(s->for_body, assoc_names, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForAssocSlice(ci.body, assoc_names, diag);
}

void Elaborator::ValidateAssocArraySlices(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> assoc_names;
  for (const auto& [name, info] : var_array_info_) {
    if (info.is_assoc) assoc_names.insert(name);
  }
  if (assoc_names.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckAssocSliceExpr(item->assign_lhs, assoc_names, diag_);
      CheckAssocSliceExpr(item->assign_rhs, assoc_names, diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForAssocSlice(item->body, assoc_names, diag_);
    }
  }
}

static bool IsTraversalMethod(std::string_view name) {
  return name == "first" || name == "last" || name == "next" || name == "prev";
}

// §7.8.1 — array manipulation methods (§7.12) that yield an index value or an
// array of index values. A wildcard-indexed associative array may not be used
// with these, since its keys have no stable index domain to return.
static bool IsIndexReturningMethod(std::string_view name) {
  return name == "find_index" || name == "find_first_index" ||
         name == "find_last_index";
}

// §7.8.1 — true when `idx` is a nonintegral index expression for a wildcard
// associative array: a real literal, or an identifier of a real/shortreal/
// realtime variable. (A string literal is not nonintegral here; it is cast to
// an equivalent-width bit vector.)
bool IsNonintegralIndex(const Expr* idx, const TypeMap& var_types) {
  if (!idx) return false;
  if (idx->kind == ExprKind::kRealLiteral) return true;
  if (idx->kind == ExprKind::kIdentifier) {
    auto it = var_types.find(idx->text);
    return it != var_types.end() && IsRealType(it->second);
  }
  return false;
}

static void CheckWildcardTraversalExpr(
    const Expr* e, const std::unordered_set<std::string_view>& wildcard_names,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kCall && e->base &&
      e->base->kind == ExprKind::kIdentifier && IsTraversalMethod(e->callee) &&
      wildcard_names.count(e->base->text)) {
    diag.Error(e->range.start,
               std::format("'{}' is not allowed on wildcard associative "
                           "array '{}'",
                           e->callee, e->base->text));
  }
  // §7.8.1 — an array-locator method (e.g. `aa.find_index with (...)`) parses
  // as a member access whose receiver is the array and whose member is the
  // method name. Reject the index-returning locators on a wildcard array.
  if (e->kind == ExprKind::kMemberAccess && e->lhs &&
      e->lhs->kind == ExprKind::kIdentifier && e->rhs &&
      IsIndexReturningMethod(e->rhs->text) &&
      wildcard_names.count(e->lhs->text)) {
    diag.Error(e->range.start,
               std::format("'{}' is not allowed on wildcard associative "
                           "array '{}'",
                           e->rhs->text, e->lhs->text));
  }
  // §7.8.1 — a wildcard index must be integral; a real (nonintegral) value used
  // to index the array is illegal.
  if (e->kind == ExprKind::kSelect && e->base &&
      e->base->kind == ExprKind::kIdentifier &&
      IsNonintegralIndex(e->index, var_types) &&
      wildcard_names.count(e->base->text)) {
    diag.Error(e->index->range.start,
               std::format("nonintegral index is not allowed on wildcard "
                           "associative array '{}'",
                           e->base->text));
  }
  CheckWildcardTraversalExpr(e->lhs, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->rhs, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->base, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->index, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->index_end, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->condition, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->true_expr, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(e->false_expr, wildcard_names, var_types, diag);
  for (const auto* elem : e->elements) {
    CheckWildcardTraversalExpr(elem, wildcard_names, var_types, diag);
  }
}

static void WalkStmtsForWildcardTraversal(
    const Stmt* s, const std::unordered_set<std::string_view>& wildcard_names,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!s) return;
  // §7.8.1 — a wildcard-indexed associative array may not drive a foreach loop.
  if (s->kind == StmtKind::kForeach && s->expr &&
      (s->expr->kind == ExprKind::kIdentifier ||
       s->expr->kind == ExprKind::kMemberAccess) &&
      wildcard_names.count(s->expr->text)) {
    diag.Error(s->range.start,
               std::format("wildcard associative array '{}' may not be used in "
                           "a foreach loop",
                           s->expr->text));
  }
  CheckWildcardTraversalExpr(s->lhs, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(s->rhs, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(s->expr, wildcard_names, var_types, diag);
  CheckWildcardTraversalExpr(s->condition, wildcard_names, var_types, diag);
  for (auto* sub : s->stmts)
    WalkStmtsForWildcardTraversal(sub, wildcard_names, var_types, diag);
  WalkStmtsForWildcardTraversal(s->then_branch, wildcard_names, var_types,
                                diag);
  WalkStmtsForWildcardTraversal(s->else_branch, wildcard_names, var_types,
                                diag);
  WalkStmtsForWildcardTraversal(s->body, wildcard_names, var_types, diag);
  WalkStmtsForWildcardTraversal(s->for_body, wildcard_names, var_types, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForWildcardTraversal(ci.body, wildcard_names, var_types, diag);
}

void Elaborator::ValidateAssocWildcardTraversal(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> wildcard_names;
  for (const auto& [name, info] : var_array_info_) {
    if (info.is_assoc && info.assoc_index_type == "*")
      wildcard_names.insert(name);
  }
  if (wildcard_names.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckWildcardTraversalExpr(item->assign_lhs, wildcard_names, var_types_,
                                 diag_);
      CheckWildcardTraversalExpr(item->assign_rhs, wildcard_names, var_types_,
                                 diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForWildcardTraversal(item->body, wildcard_names, var_types_,
                                    diag_);
    }
  }
}

// Section 7.9.8 -- the argument passed to one of the four associative-array
// traversal methods (first/last/next/prev) shall be assignment compatible with
// the array's index type. A string-indexed array therefore requires a string
// argument and an integral-indexed array requires an integral argument; the two
// categories are not assignment compatible with each other. A narrower integral
// argument is still assignment compatible -- the resulting truncation is
// resolved at run time and is not flagged during elaboration.
enum class AssocKeyCategory : std::uint8_t { kOther, kStringKey, kIntegralKey };

static AssocKeyCategory ClassifyAssocKey(std::string_view index_type,
                                         const TypedefMap& typedefs) {
  if (index_type == "string") return AssocKeyCategory::kStringKey;
  auto builtin_integral = [](std::string_view t) {
    return t == "bit" || t == "logic" || t == "reg" || t == "byte" ||
           t == "shortint" || t == "int" || t == "longint" || t == "integer" ||
           t == "time";
  };
  if (builtin_integral(index_type)) return AssocKeyCategory::kIntegralKey;
  auto it = typedefs.find(index_type);
  if (it != typedefs.end() && IsIntegralType(it->second.kind))
    return AssocKeyCategory::kIntegralKey;
  return AssocKeyCategory::kOther;
}

static bool TraversalArgIsString(const Expr* arg, const TypeMap& var_types) {
  if (!arg || arg->kind != ExprKind::kIdentifier) return false;
  auto it = var_types.find(arg->text);
  return it != var_types.end() && it->second == DataTypeKind::kString;
}

static bool TraversalArgIsIntegral(const Expr* arg, const TypeMap& var_types) {
  if (!arg || arg->kind != ExprKind::kIdentifier) return false;
  auto it = var_types.find(arg->text);
  return it != var_types.end() && IsIntegralType(it->second);
}

static void CheckTraversalArgTypeExpr(
    const Expr* e,
    const std::unordered_map<std::string_view, AssocKeyCategory>& assoc_keys,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kCall && e->base &&
      e->base->kind == ExprKind::kIdentifier && IsTraversalMethod(e->callee) &&
      !e->args.empty()) {
    auto it = assoc_keys.find(e->base->text);
    if (it != assoc_keys.end()) {
      const Expr* arg = e->args[0];
      bool wrong = (it->second == AssocKeyCategory::kStringKey &&
                    TraversalArgIsIntegral(arg, var_types)) ||
                   (it->second == AssocKeyCategory::kIntegralKey &&
                    TraversalArgIsString(arg, var_types));
      if (wrong) {
        diag.Error(arg ? arg->range.start : e->range.start,
                   std::format("traversal method '{}' argument is not "
                               "assignment compatible with the index type of "
                               "associative array '{}'",
                               e->callee, e->base->text));
      }
    }
  }
  CheckTraversalArgTypeExpr(e->lhs, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->rhs, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->base, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->index, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->index_end, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->condition, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->true_expr, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(e->false_expr, assoc_keys, var_types, diag);
  for (const auto* a : e->args)
    CheckTraversalArgTypeExpr(a, assoc_keys, var_types, diag);
  for (const auto* el : e->elems)
    CheckTraversalArgTypeExpr(el, assoc_keys, var_types, diag);
}

static void WalkStmtsForTraversalArgType(
    const Stmt* s,
    const std::unordered_map<std::string_view, AssocKeyCategory>& assoc_keys,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!s) return;
  CheckTraversalArgTypeExpr(s->lhs, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(s->rhs, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(s->expr, assoc_keys, var_types, diag);
  CheckTraversalArgTypeExpr(s->condition, assoc_keys, var_types, diag);
  for (auto* sub : s->stmts)
    WalkStmtsForTraversalArgType(sub, assoc_keys, var_types, diag);
  WalkStmtsForTraversalArgType(s->then_branch, assoc_keys, var_types, diag);
  WalkStmtsForTraversalArgType(s->else_branch, assoc_keys, var_types, diag);
  WalkStmtsForTraversalArgType(s->body, assoc_keys, var_types, diag);
  WalkStmtsForTraversalArgType(s->for_body, assoc_keys, var_types, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForTraversalArgType(ci.body, assoc_keys, var_types, diag);
}

void Elaborator::ValidateAssocTraversalArgType(const ModuleDecl* decl) {
  std::unordered_map<std::string_view, AssocKeyCategory> assoc_keys;
  for (const auto& [name, info] : var_array_info_) {
    if (!info.is_assoc || info.assoc_index_type == "*") continue;
    auto cat = ClassifyAssocKey(info.assoc_index_type, typedefs_);
    if (cat != AssocKeyCategory::kOther) assoc_keys[name] = cat;
  }
  if (assoc_keys.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckTraversalArgTypeExpr(item->assign_lhs, assoc_keys, var_types_,
                                diag_);
      CheckTraversalArgTypeExpr(item->assign_rhs, assoc_keys, var_types_,
                                diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body)
      WalkStmtsForTraversalArgType(item->body, assoc_keys, var_types_, diag_);
  }
}

// §7.12.2: the array ordering methods. reverse() and shuffle() take no with
// clause, whereas sort() and rsort() accept an optional one.
static bool IsArrayOrderingMethod(std::string_view name) {
  return name == "sort" || name == "rsort" || name == "reverse" ||
         name == "shuffle";
}

static bool OrderingMethodRejectsWith(std::string_view name) {
  return name == "reverse" || name == "shuffle";
}

// Recognize an array-method invocation, in either the call form `arr.m()` or
// the property form `arr.m`. On success, `base` is the receiver expression,
// `method` is the method name, and `has_with` records whether a with clause
// was attached (the parser hangs it on the outermost expression in both
// forms).
struct OrderingMethodSite {
  const Expr* base = nullptr;
  std::string_view method;
  bool has_with = false;
};

static bool MatchOrderingMethodSite(const Expr* e, OrderingMethodSite& out) {
  if (!e) return false;
  const Expr* access = nullptr;
  if (e->kind == ExprKind::kCall && e->lhs &&
      e->lhs->kind == ExprKind::kMemberAccess) {
    access = e->lhs;
  } else if (e->kind == ExprKind::kMemberAccess) {
    access = e;
  } else {
    return false;
  }
  if (!access->lhs || !access->rhs ||
      access->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  if (!IsArrayOrderingMethod(access->rhs->text)) return false;
  out.base = access->lhs;
  out.method = access->rhs->text;
  out.has_with = e->with_expr != nullptr;
  return true;
}

// §7.12.2: ordering methods reorder any fixed or dynamically sized unpacked
// array but are not defined on associative arrays, and reverse()/shuffle()
// reject a with clause. Each is reported as a compile-time error. The
// receiver is only checked against the array tracking map when it is a plain
// identifier, which is enough to recognize a declared associative array.
static void CheckArrayOrderingExpr(
    const Expr* e,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    DiagEngine& diag) {
  if (!e) return;
  OrderingMethodSite site;
  if (MatchOrderingMethodSite(e, site) && site.base &&
      site.base->kind == ExprKind::kIdentifier) {
    auto it = var_array_info.find(site.base->text);
    if (it != var_array_info.end()) {
      if (it->second.is_assoc) {
        diag.Error(e->range.start,
                   std::format("array ordering method '{}' cannot be applied "
                               "to associative array '{}'",
                               site.method, site.base->text));
      } else if (site.has_with && OrderingMethodRejectsWith(site.method)) {
        diag.Error(e->range.start,
                   std::format("array ordering method '{}' does not accept a "
                               "'with' clause",
                               site.method));
      }
    }
  }
  CheckArrayOrderingExpr(e->lhs, var_array_info, diag);
  CheckArrayOrderingExpr(e->rhs, var_array_info, diag);
  CheckArrayOrderingExpr(e->base, var_array_info, diag);
  CheckArrayOrderingExpr(e->index, var_array_info, diag);
  CheckArrayOrderingExpr(e->condition, var_array_info, diag);
  CheckArrayOrderingExpr(e->true_expr, var_array_info, diag);
  CheckArrayOrderingExpr(e->false_expr, var_array_info, diag);
  for (const auto* a : e->args) CheckArrayOrderingExpr(a, var_array_info, diag);
  for (const auto* elem : e->elements)
    CheckArrayOrderingExpr(elem, var_array_info, diag);
}

static void WalkStmtsForArrayOrdering(
    const Stmt* s,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    DiagEngine& diag) {
  if (!s) return;
  CheckArrayOrderingExpr(s->expr, var_array_info, diag);
  CheckArrayOrderingExpr(s->lhs, var_array_info, diag);
  CheckArrayOrderingExpr(s->rhs, var_array_info, diag);
  CheckArrayOrderingExpr(s->condition, var_array_info, diag);
  for (auto* sub : s->stmts)
    WalkStmtsForArrayOrdering(sub, var_array_info, diag);
  WalkStmtsForArrayOrdering(s->then_branch, var_array_info, diag);
  WalkStmtsForArrayOrdering(s->else_branch, var_array_info, diag);
  WalkStmtsForArrayOrdering(s->body, var_array_info, diag);
  WalkStmtsForArrayOrdering(s->for_body, var_array_info, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForArrayOrdering(ci.body, var_array_info, diag);
}

void Elaborator::ValidateArrayOrderingMethods(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckArrayOrderingExpr(item->assign_lhs, var_array_info_, diag_);
      CheckArrayOrderingExpr(item->assign_rhs, var_array_info_, diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForArrayOrdering(item->body, var_array_info_, diag_);
    }
  }
}

}  // namespace delta
