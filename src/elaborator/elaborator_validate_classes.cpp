#include <algorithm>
#include <cmath>
#include <format>
#include <functional>
#include <optional>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

using TypeMap = std::unordered_map<std::string_view, DataTypeKind>;

static bool IsCompoundAssignOp(TokenKind op) {
  switch (op) {
    case TokenKind::kPlusEq:
    case TokenKind::kMinusEq:
    case TokenKind::kStarEq:
    case TokenKind::kSlashEq:
    case TokenKind::kPercentEq:
    case TokenKind::kAmpEq:
    case TokenKind::kPipeEq:
    case TokenKind::kCaretEq:
    case TokenKind::kLtLtEq:
    case TokenKind::kGtGtEq:
    case TokenKind::kLtLtLtEq:
    case TokenKind::kGtGtGtEq:
      return true;
    default:
      return false;
  }
}

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
  if (l.is_assoc && r.is_assoc &&
      l.assoc_index_type != r.assoc_index_type) {
    diag_.Error(loc, "associative array index type mismatch in assignment");
    return;
  }

  if (l.num_unpacked_dims != r.num_unpacked_dims) {
    diag_.Error(loc,
                std::format("array assignment requires the same number of "
                            "unpacked dimensions ('{}' has {}, '{}' has {})",
                            lhs->text, l.num_unpacked_dims,
                            rhs->text, r.num_unpacked_dims));
    return;
  }

  if (!ElementTypesEquivalent(l.elem_type, l.elem_width, l.elem_is_signed,
                              l.elem_is_4state, r.elem_type, r.elem_width,
                              r.elem_is_signed, r.elem_is_4state)) {
    diag_.Error(loc,
                std::format("array element type mismatch in assignment "
                            "('{}' vs '{}')",
                            lhs->text, rhs->text));
    return;
  }
  if (l.unpacked_size > 0 && !l.is_dynamic && r.unpacked_size > 0 &&
      !r.is_dynamic && l.unpacked_size != r.unpacked_size) {
    diag_.Error(loc,
                std::format("array size mismatch: '{}' has {} elements but "
                            "'{}' has {}",
                            lhs->text, l.unpacked_size,
                            rhs->text, r.unpacked_size));
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
  WalkStmtForArrayArgTypes(s->for_body, func_decls, var_array_info,
                           class_names, typedefs, diag);
  for (auto* fs : s->for_steps)
    WalkStmtForArrayArgTypes(fs, func_decls, var_array_info, class_names,
                             typedefs, diag);
  WalkExprForArrayArgTypes(s->for_cond, func_decls, var_array_info,
                           class_names, typedefs, diag);
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

static bool IsSliceSelect(const Expr* e) {
  if (!e || e->kind != ExprKind::kSelect) return false;
  return e->is_part_select_plus || e->is_part_select_minus || e->index_end;
}

static void CheckAssocSliceExpr(
    const Expr* e,
    const std::unordered_set<std::string_view>& assoc_names,
    DiagEngine& diag) {
  if (!e) return;
  if (IsSliceSelect(e) && e->base &&
      e->base->kind == ExprKind::kIdentifier) {
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
    const Stmt* s,
    const std::unordered_set<std::string_view>& assoc_names,
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
  for (auto& ci : s->case_items) WalkStmtsForAssocSlice(ci.body, assoc_names, diag);
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
static bool IsNonintegralIndex(const Expr* idx, const TypeMap& var_types) {
  if (!idx) return false;
  if (idx->kind == ExprKind::kRealLiteral) return true;
  if (idx->kind == ExprKind::kIdentifier) {
    auto it = var_types.find(idx->text);
    return it != var_types.end() && IsRealType(it->second);
  }
  return false;
}

static void CheckWildcardTraversalExpr(
    const Expr* e,
    const std::unordered_set<std::string_view>& wildcard_names,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kCall && e->base &&
      e->base->kind == ExprKind::kIdentifier &&
      IsTraversalMethod(e->callee) && wildcard_names.count(e->base->text)) {
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
    const Stmt* s,
    const std::unordered_set<std::string_view>& wildcard_names,
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
  WalkStmtsForWildcardTraversal(s->then_branch, wildcard_names, var_types, diag);
  WalkStmtsForWildcardTraversal(s->else_branch, wildcard_names, var_types, diag);
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
enum class AssocKeyCategory { kOther, kStringKey, kIntegralKey };

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
      bool wrong =
          (it->second == AssocKeyCategory::kStringKey &&
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
      CheckTraversalArgTypeExpr(item->assign_lhs, assoc_keys, var_types_, diag_);
      CheckTraversalArgTypeExpr(item->assign_rhs, assoc_keys, var_types_, diag_);
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

static bool IsClassDerivedFrom(std::string_view a, std::string_view b,
                               const CompilationUnit* unit);

static bool IsLiteralExpr(ExprKind kind) {
  return kind == ExprKind::kIntegerLiteral ||
         kind == ExprKind::kRealLiteral || kind == ExprKind::kTimeLiteral ||
         kind == ExprKind::kStringLiteral ||
         kind == ExprKind::kUnbasedUnsizedLiteral;
}

// §7.8.3: an associative array declared with a class index may only be
// indexed by an object of that class or a class derived from it; a null
// handle is also valid. Any other index expression is a type error.
static void CheckClassIndexSelectExpr(
    const Expr* e,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const std::unordered_map<std::string_view, std::string_view>&
        class_var_types,
    const std::unordered_set<std::string_view>& class_names,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base && e->index &&
      e->base->kind == ExprKind::kIdentifier) {
    auto it = var_array_info.find(e->base->text);
    if (it != var_array_info.end() && it->second.is_assoc &&
        class_names.count(it->second.assoc_index_type) > 0) {
      const Expr* idx = e->index;
      auto index_class = it->second.assoc_index_type;
      bool is_null =
          idx->kind == ExprKind::kIdentifier && idx->text == "null";
      bool illegal = false;
      if (!is_null) {
        if (IsLiteralExpr(idx->kind)) {
          illegal = true;
        } else if (idx->kind == ExprKind::kIdentifier) {
          auto vt = class_var_types.find(idx->text);
          if (vt != class_var_types.end() &&
              !IsClassDerivedFrom(vt->second, index_class, unit)) {
            illegal = true;
          }
        }
      }
      if (illegal) {
        diag.Error(
            e->range.start,
            std::format("class-indexed associative array '{}' shall be "
                        "indexed by an object of class '{}' or a derived class",
                        e->base->text, index_class));
      }
    }
  }
  CheckClassIndexSelectExpr(e->lhs, var_array_info, class_var_types,
                            class_names, unit, diag);
  CheckClassIndexSelectExpr(e->rhs, var_array_info, class_var_types,
                            class_names, unit, diag);
  CheckClassIndexSelectExpr(e->base, var_array_info, class_var_types,
                            class_names, unit, diag);
  CheckClassIndexSelectExpr(e->index, var_array_info, class_var_types,
                            class_names, unit, diag);
  CheckClassIndexSelectExpr(e->condition, var_array_info, class_var_types,
                            class_names, unit, diag);
  CheckClassIndexSelectExpr(e->true_expr, var_array_info, class_var_types,
                            class_names, unit, diag);
  CheckClassIndexSelectExpr(e->false_expr, var_array_info, class_var_types,
                            class_names, unit, diag);
  for (const auto* elem : e->elements) {
    CheckClassIndexSelectExpr(elem, var_array_info, class_var_types,
                              class_names, unit, diag);
  }
}

static void WalkStmtsForClassIndexSelect(
    const Stmt* s,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const std::unordered_map<std::string_view, std::string_view>&
        class_var_types,
    const std::unordered_set<std::string_view>& class_names,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (!s) return;
  CheckClassIndexSelectExpr(s->lhs, var_array_info, class_var_types,
                            class_names, unit, diag);
  CheckClassIndexSelectExpr(s->rhs, var_array_info, class_var_types,
                            class_names, unit, diag);
  CheckClassIndexSelectExpr(s->expr, var_array_info, class_var_types,
                            class_names, unit, diag);
  CheckClassIndexSelectExpr(s->condition, var_array_info, class_var_types,
                            class_names, unit, diag);
  for (auto* sub : s->stmts)
    WalkStmtsForClassIndexSelect(sub, var_array_info, class_var_types,
                                 class_names, unit, diag);
  WalkStmtsForClassIndexSelect(s->then_branch, var_array_info, class_var_types,
                               class_names, unit, diag);
  WalkStmtsForClassIndexSelect(s->else_branch, var_array_info, class_var_types,
                               class_names, unit, diag);
  WalkStmtsForClassIndexSelect(s->body, var_array_info, class_var_types,
                               class_names, unit, diag);
  WalkStmtsForClassIndexSelect(s->for_body, var_array_info, class_var_types,
                               class_names, unit, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForClassIndexSelect(ci.body, var_array_info, class_var_types,
                                 class_names, unit, diag);
}

void Elaborator::ValidateClassIndexSelect(const ModuleDecl* decl) {
  bool has_class_index = false;
  for (const auto& entry : var_array_info_) {
    const auto& info = entry.second;
    if (info.is_assoc && class_names_.count(info.assoc_index_type) > 0) {
      has_class_index = true;
      break;
    }
  }
  if (!has_class_index) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckClassIndexSelectExpr(item->assign_lhs, var_array_info_,
                                class_var_types_, class_names_, unit_, diag_);
      CheckClassIndexSelectExpr(item->assign_rhs, var_array_info_,
                                class_var_types_, class_names_, unit_, diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForClassIndexSelect(item->body, var_array_info_,
                                   class_var_types_, class_names_, unit_,
                                   diag_);
    }
  }
}

// §7.8.2: an associative array declared with a string index may only be
// indexed by a string or a string literal of any length. Any other index
// expression type is a type check error. An empty string literal is a string
// literal and therefore valid.
static void CheckStringIndexSelectExpr(
    const Expr* e,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!e) return;
  // Plain element selects only; a slice on an associative array is reported
  // separately, so skip it here to avoid a second diagnostic on one site.
  if (e->kind == ExprKind::kSelect && e->base && e->index &&
      e->base->kind == ExprKind::kIdentifier && !IsSliceSelect(e)) {
    auto it = var_array_info.find(e->base->text);
    if (it != var_array_info.end() && it->second.is_assoc &&
        it->second.assoc_index_type == "string") {
      const Expr* idx = e->index;
      bool illegal = false;
      if (idx->kind == ExprKind::kStringLiteral) {
        // A string literal of any length, including "", is a valid index.
      } else if (IsLiteralExpr(idx->kind)) {
        // Any other literal (integer, real, time, unbased-unsized) is a
        // different type.
        illegal = true;
      } else if (idx->kind == ExprKind::kIdentifier) {
        auto vt = var_types.find(idx->text);
        if (vt != var_types.end() && vt->second != DataTypeKind::kString) {
          illegal = true;
        }
      }
      if (illegal) {
        diag.Error(
            e->range.start,
            std::format("string-indexed associative array '{}' shall be "
                        "indexed by a string or string literal",
                        e->base->text));
      }
    }
  }
  CheckStringIndexSelectExpr(e->lhs, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(e->rhs, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(e->base, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(e->index, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(e->condition, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(e->true_expr, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(e->false_expr, var_array_info, var_types, diag);
  for (const auto* elem : e->elements) {
    CheckStringIndexSelectExpr(elem, var_array_info, var_types, diag);
  }
}

static void WalkStmtsForStringIndexSelect(
    const Stmt* s,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!s) return;
  CheckStringIndexSelectExpr(s->lhs, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(s->rhs, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(s->expr, var_array_info, var_types, diag);
  CheckStringIndexSelectExpr(s->condition, var_array_info, var_types, diag);
  for (auto* sub : s->stmts)
    WalkStmtsForStringIndexSelect(sub, var_array_info, var_types, diag);
  WalkStmtsForStringIndexSelect(s->then_branch, var_array_info, var_types, diag);
  WalkStmtsForStringIndexSelect(s->else_branch, var_array_info, var_types, diag);
  WalkStmtsForStringIndexSelect(s->body, var_array_info, var_types, diag);
  WalkStmtsForStringIndexSelect(s->for_body, var_array_info, var_types, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForStringIndexSelect(ci.body, var_array_info, var_types, diag);
}

void Elaborator::ValidateStringIndexSelect(const ModuleDecl* decl) {
  bool has_string_index = false;
  for (const auto& entry : var_array_info_) {
    const auto& info = entry.second;
    if (info.is_assoc && info.assoc_index_type == "string") {
      has_string_index = true;
      break;
    }
  }
  if (!has_string_index) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckStringIndexSelectExpr(item->assign_lhs, var_array_info_, var_types_,
                                 diag_);
      CheckStringIndexSelectExpr(item->assign_rhs, var_array_info_, var_types_,
                                 diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForStringIndexSelect(item->body, var_array_info_, var_types_,
                                    diag_);
    }
  }
}

// §7.8.4: indexing an integral-index associative array casts the index
// expression to the index type, but an implicit cast from a real or shortreal
// expression is illegal. Flag any element select on such an array whose index
// is a nonintegral (real) expression.
static void CheckIntegralIndexSelectExpr(
    const Expr* e,
    const std::unordered_set<std::string_view>& integral_names,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base && e->index &&
      e->base->kind == ExprKind::kIdentifier && !IsSliceSelect(e) &&
      integral_names.count(e->base->text) &&
      IsNonintegralIndex(e->index, var_types)) {
    diag.Error(e->index->range.start,
               std::format("real or shortreal index is not allowed on "
                           "integral-indexed associative array '{}'",
                           e->base->text));
  }
  CheckIntegralIndexSelectExpr(e->lhs, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(e->rhs, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(e->base, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(e->index, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(e->condition, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(e->true_expr, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(e->false_expr, integral_names, var_types, diag);
  for (const auto* elem : e->elements) {
    CheckIntegralIndexSelectExpr(elem, integral_names, var_types, diag);
  }
}

static void WalkStmtsForIntegralIndexSelect(
    const Stmt* s,
    const std::unordered_set<std::string_view>& integral_names,
    const TypeMap& var_types, DiagEngine& diag) {
  if (!s) return;
  CheckIntegralIndexSelectExpr(s->lhs, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(s->rhs, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(s->expr, integral_names, var_types, diag);
  CheckIntegralIndexSelectExpr(s->condition, integral_names, var_types, diag);
  for (auto* sub : s->stmts)
    WalkStmtsForIntegralIndexSelect(sub, integral_names, var_types, diag);
  WalkStmtsForIntegralIndexSelect(s->then_branch, integral_names, var_types,
                                  diag);
  WalkStmtsForIntegralIndexSelect(s->else_branch, integral_names, var_types,
                                  diag);
  WalkStmtsForIntegralIndexSelect(s->body, integral_names, var_types, diag);
  WalkStmtsForIntegralIndexSelect(s->for_body, integral_names, var_types, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForIntegralIndexSelect(ci.body, integral_names, var_types, diag);
}

void Elaborator::ValidateIntegralIndexSelect(const ModuleDecl* decl) {
  auto is_builtin_integral = [](std::string_view t) {
    return t == "int" || t == "integer" || t == "byte" || t == "shortint" ||
           t == "longint";
  };
  std::unordered_set<std::string_view> integral_names;
  for (const auto& [name, info] : var_array_info_) {
    if (!info.is_assoc) continue;
    auto t = info.assoc_index_type;
    if (t == "string" || t == "*" || class_names_.count(t)) continue;
    bool integral = is_builtin_integral(t);
    if (!integral) {
      auto it = typedefs_.find(t);
      integral = it != typedefs_.end() && IsIntegralType(it->second.kind);
    }
    if (integral) integral_names.insert(name);
  }
  if (integral_names.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckIntegralIndexSelectExpr(item->assign_lhs, integral_names, var_types_,
                                   diag_);
      CheckIntegralIndexSelectExpr(item->assign_rhs, integral_names, var_types_,
                                   diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForIntegralIndexSelect(item->body, integral_names, var_types_,
                                      diag_);
    }
  }
}

static bool ContainsRealType(const DataType& dtype, const TypedefMap& tds,
                             int depth = 0) {
  // Guard against a pathological recursive typedef chain; a legitimate type
  // nests only a handful of levels deep.
  if (depth > 16) return false;
  if (dtype.kind == DataTypeKind::kNamed) {
    auto it = tds.find(dtype.type_name);
    if (it != tds.end()) return ContainsRealType(it->second, tds, depth + 1);
    return false;
  }
  if (IsRealType(dtype.kind)) return true;
  for (const auto& m : dtype.struct_members) {
    if (IsRealType(m.type_kind)) return true;
    // A member written through a typedef only reveals a real after the alias is
    // resolved, so follow a named member type into the typedef table and check
    // whatever it ultimately denotes (including a nested struct that holds one).
    if (m.type_kind == DataTypeKind::kNamed) {
      auto it = tds.find(m.type_name);
      if (it != tds.end() && ContainsRealType(it->second, tds, depth + 1))
        return true;
    }
  }
  return false;
}

void Elaborator::ValidateAssocIndexType(const ModuleItem* item) {
  if (item->unpacked_dims.empty()) return;
  auto* dim = item->unpacked_dims[0];
  if (!dim || dim->kind != ExprKind::kIdentifier) return;
  auto t = dim->text;
  if (t == "real" || t == "shortreal" || t == "realtime") {
    diag_.Error(item->loc,
                "real or shortreal type shall not be used as an "
                "associative array index type");
    return;
  }

  auto it = typedefs_.find(t);
  if (it != typedefs_.end() && ContainsRealType(it->second, typedefs_)) {
    diag_.Error(item->loc,
                "real or shortreal type shall not be used as an "
                "associative array index type");
  }
}

static bool IsClassVar(const Expr* e,
                       const std::unordered_set<std::string_view>& class_vars) {
  auto name = ExprIdent(e);
  if (name.empty()) return false;
  return class_vars.count(name) != 0;
}

static bool IsAllowedClassBinaryOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq ||
         op == TokenKind::kEqEqQuestion || op == TokenKind::kBangEqQuestion;
}

static bool IsClassDerivedFrom(std::string_view a, std::string_view b,
                               const CompilationUnit* unit) {
  if (a == b) return true;
  for (const auto* cls = FindClassDecl(a, unit); cls;
       cls = cls->base_class.empty() ? nullptr
                                     : FindClassDecl(cls->base_class, unit)) {
    if (cls->base_class == b) return true;
    for (const auto& iface : cls->implements_types) {
      if (IsClassDerivedFrom(iface.name, b, unit)) return true;
    }
    for (const auto& iface : cls->extends_interfaces) {
      if (IsClassDerivedFrom(iface.name, b, unit)) return true;
    }
  }
  return false;
}

static bool AreClassTypesComparable(
    std::string_view type_a, std::string_view type_b,
    const CompilationUnit* unit) {
  return IsClassDerivedFrom(type_a, type_b, unit) ||
         IsClassDerivedFrom(type_b, type_a, unit);
}

// §8.8: a typed constructor call writes the class scope before 'new' to fix
// the constructed object's type independently of the assignment target (e.g.
// Derived::new or Param#(...)::new). Return that scope type name when *rhs*
// is such a call, otherwise an empty view. The argument-less form is parsed
// as a bare scope-resolved member access; the parenthesized form is a call
// whose callee is that member access.
static std::string_view TypedConstructorScopeType(const Expr* rhs) {
  if (!rhs) return {};
  const Expr* access = nullptr;
  if (rhs->kind == ExprKind::kMemberAccess) {
    access = rhs;
  } else if (rhs->kind == ExprKind::kCall && rhs->lhs &&
             rhs->lhs->kind == ExprKind::kMemberAccess) {
    access = rhs->lhs;
  }
  if (!access) return {};
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier) return {};
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return {};
  if (access->rhs->text != "new") return {};
  return access->lhs->text;
}

static void CheckClassHandleExpr(
    const Expr* e, const std::unordered_set<std::string_view>& class_vars,
    const std::unordered_map<std::string_view, std::string_view>&
        class_var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (!e) return;

  if (e->kind == ExprKind::kBinary) {
    bool lhs_class = e->lhs && IsClassVar(e->lhs, class_vars);
    bool rhs_class = e->rhs && IsClassVar(e->rhs, class_vars);
    if ((lhs_class || rhs_class) && !IsAllowedClassBinaryOp(e->op)) {
      diag.Error(e->range.start,
                 "operator is not allowed on class object handles");
    }

    if (lhs_class && rhs_class && IsAllowedClassBinaryOp(e->op)) {
      auto lhs_name = ExprIdent(e->lhs);
      auto rhs_name = ExprIdent(e->rhs);
      auto lt = class_var_types.find(lhs_name);
      auto rt = class_var_types.find(rhs_name);
      if (lt != class_var_types.end() && rt != class_var_types.end() &&
          !AreClassTypesComparable(lt->second, rt->second, unit)) {
        diag.Error(e->range.start,
                   "class handle comparison requires assignment compatible "
                   "types");
      }
    }
  }

  if (e->kind == ExprKind::kUnary && IsClassVar(e->lhs, class_vars)) {
    diag.Error(e->range.start,
               "operator is not allowed on class object handles");
  }

  if (e->kind == ExprKind::kPostfixUnary && IsClassVar(e->lhs, class_vars)) {
    diag.Error(e->range.start,
               "operator is not allowed on class object handles");
  }

  if (e->kind == ExprKind::kSelect && e->base &&
      IsClassVar(e->base, class_vars)) {
    diag.Error(e->range.start, "bit-select on class object handle is illegal");
  }

  if (e->kind == ExprKind::kCast && e->lhs && IsClassVar(e->lhs, class_vars) &&
      !e->text.empty() && !FindClassDecl(e->text, unit)) {
    diag.Error(e->range.start,
               "cannot cast class object handle to a non-class type");
  }

  if (e->kind == ExprKind::kCast && !e->text.empty() &&
      FindClassDecl(e->text, unit) != nullptr && e->lhs &&
      !IsClassVar(e->lhs, class_vars) &&
      !(e->lhs->kind == ExprKind::kIdentifier && e->lhs->text == "null")) {
    diag.Error(e->range.start,
               "cannot cast non-class value to a class type");
  }

  CheckClassHandleExpr(e->lhs, class_vars, class_var_types, unit, diag);
  CheckClassHandleExpr(e->rhs, class_vars, class_var_types, unit, diag);
  CheckClassHandleExpr(e->base, class_vars, class_var_types, unit, diag);
  CheckClassHandleExpr(e->index, class_vars, class_var_types, unit, diag);
  CheckClassHandleExpr(e->condition, class_vars, class_var_types, unit, diag);
  CheckClassHandleExpr(e->true_expr, class_vars, class_var_types, unit, diag);
  CheckClassHandleExpr(e->false_expr, class_vars, class_var_types, unit, diag);
  for (const auto* elem : e->elements) {
    CheckClassHandleExpr(elem, class_vars, class_var_types, unit, diag);
  }
}

static void CheckInterfaceHandleRandConstraintMode(
    const Stmt* s,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (!s) return;

  const Expr* call = nullptr;
  if (s->kind == StmtKind::kExprStmt && s->expr) {
    call = s->expr;
  } else if ((s->kind == StmtKind::kBlockingAssign ||
              s->kind == StmtKind::kNonblockingAssign) &&
             s->rhs) {
    call = s->rhs;
  }

  if (call && call->kind == ExprKind::kCast && call->lhs) call = call->lhs;
  if (!call || call->kind != ExprKind::kCall) return;
  const Expr* callee = call->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return;
  if (!callee->lhs || callee->lhs->kind != ExprKind::kIdentifier) return;
  if (!callee->rhs || callee->rhs->kind != ExprKind::kIdentifier) return;
  auto method_name = callee->rhs->text;
  if (method_name != "rand_mode" && method_name != "constraint_mode") return;
  auto var_name = callee->lhs->text;
  auto it = var_types.find(var_name);
  if (it == var_types.end()) return;
  const auto* cls = FindClassDecl(it->second, unit);
  if (!cls || !cls->is_interface) return;
  diag.Error(callee->range.start,
             std::format("'{}' is not legal on interface class handle '{}'",
                         method_name, var_name));
}

// 18.9: the constraint named in a constraint_mode() call shall be a constraint
// block that exists in the object's class hierarchy; naming one that does not
// exist is a compile-time error. This applies only to the named form
// obj.constraint_id.constraint_mode(...). The check resolves the object handle
// to its class type; when the type cannot be resolved it stays silent, so the
// error is reported only when the absence of the block is certain.
static void CheckNamedConstraintModeExists(
    const Stmt* s,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (!s) return;

  const Expr* call = nullptr;
  if (s->kind == StmtKind::kExprStmt && s->expr) {
    call = s->expr;
  } else if ((s->kind == StmtKind::kBlockingAssign ||
              s->kind == StmtKind::kNonblockingAssign) &&
             s->rhs) {
    call = s->rhs;
  }
  if (call && call->kind == ExprKind::kCast && call->lhs) call = call->lhs;
  if (!call || call->kind != ExprKind::kCall) return;

  // callee must be <object>.<constraint_id>.constraint_mode
  const Expr* callee = call->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return;
  if (!callee->rhs || callee->rhs->kind != ExprKind::kIdentifier) return;
  if (callee->rhs->text != "constraint_mode") return;

  // The named form prefixes the method with object.constraint_id, so the
  // receiver of constraint_mode is itself a member access whose left side is a
  // plain object handle and whose right side is the constraint name.
  const Expr* prefix = callee->lhs;
  if (!prefix || prefix->kind != ExprKind::kMemberAccess) return;
  if (!prefix->lhs || prefix->lhs->kind != ExprKind::kIdentifier) return;
  if (!prefix->rhs || prefix->rhs->kind != ExprKind::kIdentifier) return;

  auto obj_name = prefix->lhs->text;
  auto constraint_name = prefix->rhs->text;

  auto it = var_types.find(obj_name);
  if (it == var_types.end()) return;
  const auto* cls = FindClassDecl(it->second, unit);
  if (!cls || cls->is_interface) return;

  // Walk the class and its base classes for a constraint block of that name.
  for (const auto* c = cls; c;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kConstraint &&
          m->name == constraint_name) {
        return;
      }
    }
  }

  diag.Error(prefix->rhs->range.start,
             std::format("constraint '{}' does not exist in the hierarchy of "
                         "class '{}'",
                         constraint_name, it->second));
}

void Elaborator::WalkStmtsForClassHandleOps(const Stmt* s) {
  if (!s) return;

  if (s->kind == StmtKind::kVarDecl &&
      s->var_decl_type.kind == DataTypeKind::kNamed &&
      class_names_.count(s->var_decl_type.type_name)) {
    class_var_names_.insert(s->var_name);
    class_var_types_[s->var_name] = s->var_decl_type.type_name;
  }

  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && IsClassVar(s->lhs, class_var_names_)) {
    if (s->rhs && s->rhs->kind == ExprKind::kBinary &&
        IsCompoundAssignOp(s->rhs->op)) {
      diag_.Error(s->range.start,
                  "operator is not allowed on class object handles");
    }

    if (s->rhs && s->rhs->kind == ExprKind::kCall && s->rhs->text == "new") {
      auto lhs_name = ExprIdent(s->lhs);
      auto lt = class_var_types_.find(lhs_name);
      if (lt != class_var_types_.end()) {
        if (lt->second == "process") {
          diag_.Error(s->range.start,
                      "cannot construct a process object with 'new'");
        } else {
          const auto* cls = FindClassDecl(lt->second, unit_);
          if (cls && cls->is_interface) {
            diag_.Error(s->range.start,
                        std::format("cannot construct object of interface class "
                                    "'{}'",
                                    cls->name));
          }
        }
      }
    }

    // §8.8: a typed constructor call may name a type different from the
    // assignment target, but that specified type shall be assignment
    // compatible with the target — i.e. the same class or one derived from
    // it. Reject a scope type that is an unrelated class.
    auto specified = TypedConstructorScopeType(s->rhs);
    if (!specified.empty() && class_names_.count(specified)) {
      auto lhs_name = ExprIdent(s->lhs);
      auto lt = class_var_types_.find(lhs_name);
      if (lt != class_var_types_.end() &&
          !IsClassDerivedFrom(specified, lt->second, unit_)) {
        diag_.Error(s->range.start,
                    "typed constructor call type is not assignment compatible "
                    "with the target");
      }
    }

    if (s->rhs && IsClassVar(s->rhs, class_var_names_)) {
      auto lhs_name = ExprIdent(s->lhs);
      auto rhs_name = ExprIdent(s->rhs);
      auto lt = class_var_types_.find(lhs_name);
      auto rt = class_var_types_.find(rhs_name);
      if (lt != class_var_types_.end() && rt != class_var_types_.end() &&
          !IsClassDerivedFrom(rt->second, lt->second, unit_)) {
        diag_.Error(s->range.start,
                    "class handle assignment requires assignment compatible "
                    "types");
      }
    }

    if (s->rhs && s->rhs->kind == ExprKind::kLiteral) {
      diag_.Error(s->range.start,
                  "cannot assign non-class value to class object handle");
    }
  }

  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && s->lhs->kind == ExprKind::kIdentifier &&
      !IsClassVar(s->lhs, class_var_names_) &&
      s->rhs && IsClassVar(s->rhs, class_var_names_)) {
    diag_.Error(s->range.start,
                "cannot assign class object handle to a non-class variable");
  }

  CheckInterfaceHandleRandConstraintMode(s, class_var_types_, unit_, diag_);

  CheckNamedConstraintModeExists(s, class_var_types_, unit_, diag_);

  CheckClassHandleExpr(s->rhs, class_var_names_, class_var_types_, unit_,
                       diag_);
  CheckClassHandleExpr(s->expr, class_var_names_, class_var_types_, unit_,
                       diag_);
  CheckClassHandleExpr(s->condition, class_var_names_, class_var_types_, unit_,
                       diag_);
  for (auto* sub : s->stmts) WalkStmtsForClassHandleOps(sub);
  WalkStmtsForClassHandleOps(s->then_branch);
  WalkStmtsForClassHandleOps(s->else_branch);
  WalkStmtsForClassHandleOps(s->body);
  WalkStmtsForClassHandleOps(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForClassHandleOps(ci.body);
}

void Elaborator::ValidateClassHandleOps(const ModuleDecl* decl) {
  if (class_var_names_.empty()) return;
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForClassHandleOps(item->body);
    }
  }
}

void Elaborator::ValidateClassHandleContAssign(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kContAssign) return;
  auto lhs_class =
      item->assign_lhs && IsClassVar(item->assign_lhs, class_var_names_);
  auto rhs_class =
      item->assign_rhs && IsClassVar(item->assign_rhs, class_var_names_);
  if (lhs_class || rhs_class) {
    diag_.Error(item->loc,
                "class object handle cannot be used in continuous assignment");
  }
}

static bool IsLiteralTypeOfThis(const Expr* e) {
  return e && e->kind == ExprKind::kTypeRef && e->lhs &&
         e->lhs->kind == ExprKind::kIdentifier && e->lhs->text == "this";
}

static bool ExprRefsThisOrSuper(const Expr* e) {
  if (!e) return false;
  // §8.11 lists type(this) as a permitted form alongside non-static class
  // methods, constraints, and covergroups. The cross-reference in §6.23
  // names it as a way to obtain the enclosing class type without evaluating
  // any expression, so the literal form may appear even where a bare 'this'
  // would otherwise be flagged.
  if (IsLiteralTypeOfThis(e)) return false;
  if (e->kind == ExprKind::kIdentifier &&
      (e->text == "this" || e->text == "super"))
    return true;
  if (ExprRefsThisOrSuper(e->lhs)) return true;
  if (ExprRefsThisOrSuper(e->rhs)) return true;
  if (ExprRefsThisOrSuper(e->base)) return true;
  if (ExprRefsThisOrSuper(e->index)) return true;
  if (ExprRefsThisOrSuper(e->condition)) return true;
  if (ExprRefsThisOrSuper(e->true_expr)) return true;
  if (ExprRefsThisOrSuper(e->false_expr)) return true;
  for (const auto* elem : e->elements) {
    if (ExprRefsThisOrSuper(elem)) return true;
  }
  for (const auto* arg : e->args) {
    if (ExprRefsThisOrSuper(arg)) return true;
  }
  if (ExprRefsThisOrSuper(e->with_expr)) return true;
  return false;
}

static bool StmtRefsThisOrSuper(const Stmt* s) {
  if (!s) return false;
  if (ExprRefsThisOrSuper(s->lhs)) return true;
  if (ExprRefsThisOrSuper(s->rhs)) return true;
  if (ExprRefsThisOrSuper(s->expr)) return true;
  if (ExprRefsThisOrSuper(s->condition)) return true;
  for (auto* sub : s->stmts) {
    if (StmtRefsThisOrSuper(sub)) return true;
  }
  if (StmtRefsThisOrSuper(s->then_branch)) return true;
  if (StmtRefsThisOrSuper(s->else_branch)) return true;
  if (StmtRefsThisOrSuper(s->body)) return true;
  if (StmtRefsThisOrSuper(s->for_body)) return true;
  for (auto& ci : s->case_items) {
    if (StmtRefsThisOrSuper(ci.body)) return true;
  }
  return false;
}

static void CollectLocalNames(const Stmt* s,
                              std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {
    out.insert(s->var_name);
  }
  for (auto* fi : s->for_inits) CollectLocalNames(fi, out);
  for (auto v : s->foreach_vars) {
    if (!v.empty()) out.insert(v);
  }
  for (auto* sub : s->stmts) CollectLocalNames(sub, out);
  CollectLocalNames(s->then_branch, out);
  CollectLocalNames(s->else_branch, out);
  CollectLocalNames(s->body, out);
  CollectLocalNames(s->for_body, out);
  for (auto& ci : s->case_items) CollectLocalNames(ci.body, out);
}

static bool ExprRefsNonStaticMember(
    const Expr* e,
    const std::unordered_set<std::string_view>& non_static,
    const std::unordered_set<std::string_view>& locals) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier &&
      non_static.count(e->text) && !locals.count(e->text))
    return true;
  if (e->kind == ExprKind::kCall && !e->callee.empty() &&
      non_static.count(e->callee) && !locals.count(e->callee))
    return true;
  if (ExprRefsNonStaticMember(e->lhs, non_static, locals)) return true;
  if (ExprRefsNonStaticMember(e->rhs, non_static, locals)) return true;
  if (ExprRefsNonStaticMember(e->base, non_static, locals)) return true;
  if (ExprRefsNonStaticMember(e->index, non_static, locals)) return true;
  if (ExprRefsNonStaticMember(e->condition, non_static, locals)) return true;
  if (ExprRefsNonStaticMember(e->true_expr, non_static, locals)) return true;
  if (ExprRefsNonStaticMember(e->false_expr, non_static, locals)) return true;
  for (const auto* elem : e->elements) {
    if (ExprRefsNonStaticMember(elem, non_static, locals)) return true;
  }
  for (const auto* arg : e->args) {
    if (ExprRefsNonStaticMember(arg, non_static, locals)) return true;
  }
  if (ExprRefsNonStaticMember(e->with_expr, non_static, locals)) return true;
  return false;
}

static bool StmtRefsNonStaticMember(
    const Stmt* s,
    const std::unordered_set<std::string_view>& non_static,
    const std::unordered_set<std::string_view>& locals) {
  if (!s) return false;
  if (ExprRefsNonStaticMember(s->lhs, non_static, locals)) return true;
  if (ExprRefsNonStaticMember(s->rhs, non_static, locals)) return true;
  if (ExprRefsNonStaticMember(s->expr, non_static, locals)) return true;
  if (ExprRefsNonStaticMember(s->condition, non_static, locals)) return true;
  for (auto* sub : s->stmts) {
    if (StmtRefsNonStaticMember(sub, non_static, locals)) return true;
  }
  if (StmtRefsNonStaticMember(s->then_branch, non_static, locals)) return true;
  if (StmtRefsNonStaticMember(s->else_branch, non_static, locals)) return true;
  if (StmtRefsNonStaticMember(s->body, non_static, locals)) return true;
  if (StmtRefsNonStaticMember(s->for_body, non_static, locals)) return true;
  for (auto& ci : s->case_items) {
    if (StmtRefsNonStaticMember(ci.body, non_static, locals)) return true;
  }
  return false;
}

void Elaborator::ValidateOneClassStaticMethods(const ClassDecl* cls) {

  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->is_static) continue;
    if (!m->method) continue;
    for (const auto* s : m->method->func_body_stmts) {
      if (StmtRefsThisOrSuper(s)) {
        diag_.Error(m->method->loc,
                    "'this' and 'super' shall not be used in "
                    "a static method");
        break;
      }
    }
  }

  std::unordered_set<std::string_view> non_static;
  for (const auto* member : cls->members) {
    if (member->is_static) continue;
    if (member->kind == ClassMemberKind::kProperty && !member->name.empty()) {
      non_static.insert(member->name);
    } else if (member->kind == ClassMemberKind::kMethod && member->method &&
               member->method->name != "new") {
      non_static.insert(member->method->name);
    }
  }
  if (non_static.empty()) return;

  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->is_static) continue;
    if (!m->method) continue;

    std::unordered_set<std::string_view> locals;
    for (const auto& arg : m->method->func_args) {
      if (!arg.name.empty()) locals.insert(arg.name);
    }
    if (m->method->kind == ModuleItemKind::kFunctionDecl) {
      locals.insert(m->method->name);
    }
    for (const auto* s : m->method->func_body_stmts) {
      CollectLocalNames(s, locals);
    }

    for (const auto* s : m->method->func_body_stmts) {
      if (StmtRefsNonStaticMember(s, non_static, locals)) {
        diag_.Error(m->method->loc,
                    "static method shall not access non-static members");
        break;
      }
    }
  }
}

void Elaborator::ValidateStaticMethodBodies(const ModuleDecl* decl) {
  for (const auto* cls : unit_->classes) {
    ValidateOneClassStaticMethods(cls);
  }
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
      ValidateOneClassStaticMethods(item->class_decl);
    }
  }
}

void Elaborator::ValidateThisInItem(const ModuleItem* item) {
  bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                 item->kind == ModuleItemKind::kInitialBlock;
  if (is_proc && item->body && StmtRefsThisOrSuper(item->body)) {
    diag_.Error(item->loc,
                "'this' shall only be used within non-static class methods");
    return;
  }
  bool is_func_or_task = item->kind == ModuleItemKind::kFunctionDecl ||
                         item->kind == ModuleItemKind::kTaskDecl;
  if (!is_func_or_task || item->func_body_stmts.empty()) return;
  for (const auto* s : item->func_body_stmts) {
    if (StmtRefsThisOrSuper(s)) {
      diag_.Error(item->loc,
                  "'this' shall only be used within non-static "
                  "class methods");
      return;
    }
  }
}

void Elaborator::ValidateThisUsage(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    ValidateThisInItem(item);
  }
}

void Elaborator::ValidateFinalClassExtension() {
  auto check = [&](const ClassDecl* cls) {
    if (cls->base_class.empty()) return;

    if (cls->base_class == "process") {
      diag_.Error(cls->range.start, "cannot extend a class declared ':final'");
      return;
    }
    const auto* base = FindClassDecl(cls->base_class, unit_);
    if (base && base->is_final) {
      diag_.Error(cls->range.start, "cannot extend a class declared ':final'");
    }
  };
  for (const auto* cls : unit_->classes) {
    check(cls);
  }
}

// §8.30.1: a weak_reference incorporated into another object as a class property
// carries the same parameter restriction as a standalone variable or a
// subroutine argument — its type argument shall name a class type. Any other
// type argument is a compile error, mirroring the variable-declaration and
// subroutine-argument checks elsewhere in the elaborator.
void Elaborator::ValidateWeakReferenceMembers() {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kProperty) continue;
      if (m->data_type.kind != DataTypeKind::kNamed) continue;
      if (m->data_type.type_name != "weak_reference") continue;
      if (m->data_type.type_params.empty()) continue;
      const auto& tp = m->data_type.type_params[0];
      if (tp.kind != DataTypeKind::kNamed || !class_names_.count(tp.type_name)) {
        diag_.Error(m->loc,
                    "weak_reference type parameter shall be a class type");
      }
    }
  }
}

static bool IsSuperNewCall(const Stmt* s) {
  if (!s || s->kind != StmtKind::kExprStmt || !s->expr) return false;
  const auto* call = s->expr;
  if (call->kind != ExprKind::kCall) return false;
  const auto* callee = call->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return false;
  bool lhs_is_super = callee->lhs &&
                      callee->lhs->kind == ExprKind::kIdentifier &&
                      callee->lhs->text == "super";
  bool rhs_is_new = callee->rhs && callee->rhs->kind == ExprKind::kIdentifier &&
                    callee->rhs->text == "new";
  return lhs_is_super && rhs_is_new;
}

void Elaborator::ValidateOneClassChainingCtor(const ClassDecl* cls) {
  if (cls->base_class.empty()) return;
  const ClassMember* ctor = nullptr;
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "new") {
      ctor = m;
      break;
    }
  }
  if (!ctor || !ctor->method) return;
  bool has_super_new = false;
  const auto& stmts = ctor->method->func_body_stmts;
  for (size_t i = 0; i < stmts.size(); ++i) {
    if (!IsSuperNewCall(stmts[i])) continue;
    has_super_new = true;
    if (i != 0) {
      diag_.Error(stmts[i]->range.start,
                  "super.new() shall be the first executable statement "
                  "in the constructor");
    }
    break;
  }
  if (has_super_new && (!cls->extends_args.empty() || cls->extends_has_default)) {
    diag_.Error(ctor->method->loc,
                "constructor shall not contain super.new() when extends "
                "specifier has arguments");
  }
}

// §19.4: a covergroup declared inside a class is an embedded covergroup whose
// identifier names an implicitly declared instance variable. That variable is
// instantiated by assigning the result of new() to it inside the enclosing
// class's new() method, and the standard requires it not be assigned anywhere
// outside that constructor. Any assignment to the covergroup identifier from
// another method of the same class therefore violates the rule.
static void CheckCovergroupAssignStmt(
    const Stmt* s, const std::unordered_set<std::string_view>& cg_names,
    DiagEngine& diag) {
  if (!s) return;
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && s->lhs->kind == ExprKind::kIdentifier &&
      cg_names.count(s->lhs->text)) {
    diag.Error(s->range.start,
               std::format("embedded covergroup '{}' shall only be assigned "
                           "inside the new() method of its class",
                           s->lhs->text));
  }
  for (const auto* sub : s->stmts) {
    CheckCovergroupAssignStmt(sub, cg_names, diag);
  }
  CheckCovergroupAssignStmt(s->then_branch, cg_names, diag);
  CheckCovergroupAssignStmt(s->else_branch, cg_names, diag);
  CheckCovergroupAssignStmt(s->body, cg_names, diag);
  CheckCovergroupAssignStmt(s->for_body, cg_names, diag);
  for (const auto& ci : s->case_items) {
    CheckCovergroupAssignStmt(ci.body, cg_names, diag);
  }
}

void Elaborator::ValidateEmbeddedCovergroupAssign() {
  for (const auto* cls : unit_->classes) {
    std::unordered_set<std::string_view> cg_names;
    for (const auto* m : cls->members) {
      if (m->kind == ClassMemberKind::kCovergroup && !m->name.empty()) {
        cg_names.insert(m->name);
      }
    }
    if (cg_names.empty()) continue;

    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
      // The constructor is the one place an embedded covergroup may be
      // instantiated, so assignments there are permitted.
      if (m->method->name == "new") continue;
      for (const auto* s : m->method->func_body_stmts) {
        CheckCovergroupAssignStmt(s, cg_names, diag_);
      }
    }
  }
}

// §19.4.1: a derived embedded covergroup, written `covergroup extends base ;`,
// inherits the covergroup named by `base`. It shall be an error to use the
// extends form when no covergroup of that name has previously been defined in a
// base class of the enclosing class. The search starts at the immediate base
// class and follows the inheritance chain upward; a covergroup defined in the
// derived class itself does not satisfy the requirement.
static bool BaseClassDefinesCovergroup(const ClassDecl* cls,
                                       std::string_view cg_name,
                                       const CompilationUnit* unit) {
  for (const ClassDecl* base =
           cls->base_class.empty() ? nullptr
                                   : FindClassDecl(cls->base_class, unit);
       base; base = base->base_class.empty()
                        ? nullptr
                        : FindClassDecl(base->base_class, unit)) {
    for (const auto* m : base->members) {
      if (m->kind == ClassMemberKind::kCovergroup && m->name == cg_name) {
        return true;
      }
    }
  }
  return false;
}

void Elaborator::ValidateDerivedCovergroupBase() {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kCovergroup) continue;
      if (m->covergroup_extends_base.empty()) continue;
      if (!BaseClassDefinesCovergroup(cls, m->covergroup_extends_base, unit_)) {
        diag_.Error(
            m->loc,
            std::format("derived covergroup cannot extend '{}': no covergroup "
                        "of that name is defined in a base class",
                        m->covergroup_extends_base));
      }
    }
  }
}

void Elaborator::ValidateClassMethodBodies(const ModuleDecl* decl) {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
      ValidateFunctionBody(m->method);
    }
  }
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kClassDecl || !item->class_decl) continue;
    for (const auto* m : item->class_decl->members) {
      if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
      ValidateFunctionBody(m->method);
    }
  }
}

static void ApplyAutoToClassMethods(const ClassDecl* cls) {
  if (!cls) return;
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        !m->method->is_automatic && !m->method->is_static) {
      m->method->is_automatic = true;
    }

    if (m->kind == ClassMemberKind::kClassDecl && m->nested_class) {
      ApplyAutoToClassMethods(m->nested_class);
    }
  }
}

void Elaborator::ApplyClassMethodAutomaticDefault() {
  for (auto* cls : unit_->classes) ApplyAutoToClassMethods(cls);
  for (auto* mod : unit_->modules) {
    for (auto* item : mod->items) {
      if (item->kind == ModuleItemKind::kClassDecl) {
        ApplyAutoToClassMethods(item->class_decl);
      }
    }
  }
  for (auto* pkg : unit_->packages) {
    for (auto* item : pkg->items) {
      if (item->kind == ModuleItemKind::kClassDecl) {
        ApplyAutoToClassMethods(item->class_decl);
      }
    }
  }
}

static bool ExprRefsSuper(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && e->text == "super") return true;
  if (ExprRefsSuper(e->lhs)) return true;
  if (ExprRefsSuper(e->rhs)) return true;
  if (ExprRefsSuper(e->base)) return true;
  if (ExprRefsSuper(e->index)) return true;
  if (ExprRefsSuper(e->condition)) return true;
  if (ExprRefsSuper(e->true_expr)) return true;
  if (ExprRefsSuper(e->false_expr)) return true;
  for (const auto* elem : e->elements)
    if (ExprRefsSuper(elem)) return true;
  for (const auto* arg : e->args)
    if (ExprRefsSuper(arg)) return true;
  if (ExprRefsSuper(e->with_expr)) return true;
  return false;
}

static bool StmtRefsSuper(const Stmt* s) {
  if (!s) return false;
  if (ExprRefsSuper(s->lhs)) return true;
  if (ExprRefsSuper(s->rhs)) return true;
  if (ExprRefsSuper(s->expr)) return true;
  if (ExprRefsSuper(s->condition)) return true;
  for (auto* sub : s->stmts)
    if (StmtRefsSuper(sub)) return true;
  if (StmtRefsSuper(s->then_branch)) return true;
  if (StmtRefsSuper(s->else_branch)) return true;
  if (StmtRefsSuper(s->body)) return true;
  if (StmtRefsSuper(s->for_body)) return true;
  for (auto& ci : s->case_items)
    if (StmtRefsSuper(ci.body)) return true;
  return false;
}

void Elaborator::ValidateSuperInNonDerivedClass() {
  for (const auto* cls : unit_->classes) {
    if (!cls->base_class.empty()) continue;
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
      for (const auto* s : m->method->func_body_stmts) {
        if (StmtRefsSuper(s)) {
          diag_.Error(m->method->loc,
                      "'super' shall only be used in a derived class");
          break;
        }
      }
    }
  }
}

// §8.17: returns the class's own 'new' constructor method, or null if the
// class declares none.
static const ModuleItem* FindClassCtorMethod(const ClassDecl* cls) {
  if (!cls) return nullptr;
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "new") {
      return m->method;
    }
  }
  return nullptr;
}

// §8.17: returns whether an expression tree references any identifier whose
// name appears in 'names'. Mirrors the traversal used for 'super' detection.
static bool ExprRefsAnyName(const Expr* e,
                            const std::unordered_set<std::string_view>& names) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && names.count(e->text)) return true;
  if (ExprRefsAnyName(e->lhs, names) || ExprRefsAnyName(e->rhs, names) ||
      ExprRefsAnyName(e->base, names) || ExprRefsAnyName(e->index, names) ||
      ExprRefsAnyName(e->condition, names) ||
      ExprRefsAnyName(e->true_expr, names) ||
      ExprRefsAnyName(e->false_expr, names) ||
      ExprRefsAnyName(e->with_expr, names)) {
    return true;
  }
  for (const auto* elem : e->elements)
    if (ExprRefsAnyName(elem, names)) return true;
  for (const auto* arg : e->args)
    if (ExprRefsAnyName(arg, names)) return true;
  return false;
}

// §8.17: enforces the rules governing the 'default' keyword in a subclass
// constructor argument list and in an explicit super.new() call.
void Elaborator::ValidateOneClassDefaultKeyword(const ClassDecl* cls) {
  const ModuleItem* ctor = FindClassCtorMethod(cls);

  bool ctor_has_default = false;
  if (ctor) {
    for (const auto& arg : ctor->func_args) {
      if (arg.is_default) {
        ctor_has_default = true;
        break;
      }
    }
  }

  // §8.17: 'default' expands to the superclass constructor's arguments, so the
  // class shall extend another class for the expansion to have a source.
  if (ctor_has_default && cls->base_class.empty()) {
    diag_.Error(ctor->loc,
                "'default' in a constructor argument list requires the class "
                "to extend a superclass");
  }

  // §8.17: when the extends specifier uses 'default' and the subclass also
  // defines its own constructor, that constructor's argument list shall repeat
  // the 'default' keyword.
  if (cls->extends_has_default && ctor && !ctor_has_default) {
    diag_.Error(ctor->loc,
                "constructor argument list shall contain 'default' when the "
                "extends specifier uses the 'default' keyword");
  }

  // §8.17: 'default' may be passed as the sole argument to super.new() only
  // when the constructor's own argument list used the 'default' keyword.
  if (ctor && !ctor_has_default) {
    for (const auto* s : ctor->func_body_stmts) {
      if (!IsSuperNewCall(s)) continue;
      const auto& call_args = s->expr->args;
      if (call_args.size() == 1 && call_args[0] &&
          call_args[0]->kind == ExprKind::kIdentifier &&
          call_args[0]->text == "default") {
        diag_.Error(s->range.start,
                    "'default' may be passed to super.new() only when the "
                    "constructor argument list uses the 'default' keyword");
      }
    }
  }

  if (!ctor_has_default || cls->base_class.empty()) return;

  const ClassDecl* base = FindClassDecl(cls->base_class, unit_);
  const ModuleItem* base_ctor = FindClassCtorMethod(base);
  if (!base_ctor) return;

  // §8.17: because 'default' expands to the superclass constructor arguments,
  // an explicit argument in the subclass constructor shall not share a name
  // with any superclass constructor argument.
  std::unordered_set<std::string_view> base_arg_names;
  for (const auto& a : base_ctor->func_args) {
    if (!a.name.empty()) base_arg_names.insert(a.name);
  }
  for (const auto& a : ctor->func_args) {
    if (a.is_default || a.name.empty()) continue;
    if (base_arg_names.count(a.name)) {
      diag_.Error(ctor->loc,
                  std::format("constructor argument '{}' shall not share a "
                              "name with a superclass constructor argument "
                              "when 'default' is used",
                              a.name));
    }
  }

  // §8.17: 'default' shall not be used when a superclass constructor argument's
  // default value refers to a local member of the superclass.
  std::unordered_set<std::string_view> base_locals;
  for (const auto* m : base->members) {
    if (m->is_local && !m->name.empty()) base_locals.insert(m->name);
  }
  if (!base_locals.empty()) {
    for (const auto& a : base_ctor->func_args) {
      if (a.default_value && ExprRefsAnyName(a.default_value, base_locals)) {
        diag_.Error(ctor->loc,
                    "'default' shall not be used when a superclass constructor "
                    "argument default value refers to a local member");
        break;
      }
    }
  }
}

void Elaborator::ValidateChainingConstructors() {
  for (const auto* cls : unit_->classes) {
    ValidateOneClassChainingCtor(cls);
    ValidateOneClassDefaultKeyword(cls);
  }
}

static const ClassMember* FindMemberInClass(const ClassDecl* cls,
                                            std::string_view name,
                                            const CompilationUnit* unit) {
  for (const auto* c = cls; c; ) {
    for (const auto* m : c->members) {
      if (m->name == name) return m;
    }
    if (c->base_class.empty()) break;
    c = FindClassDecl(c->base_class, unit);
  }
  return nullptr;
}

static void CheckMemberAccessVisibility(
    const Expr* e,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (e->lhs->kind != ExprKind::kIdentifier) return;
  auto it = var_types.find(e->lhs->text);
  if (it == var_types.end()) return;
  if (e->rhs->kind != ExprKind::kIdentifier) return;
  const auto* cls = FindClassDecl(it->second, unit);
  if (!cls) return;

  if (cls->type_param_names.count(e->rhs->text) > 0) {
    diag.Error(e->rhs->range.start,
               "cannot access type parameter via class handle");
    return;
  }
  const auto* m = FindMemberInClass(cls, e->rhs->text, unit);
  if (m && m->is_local) {
    diag.Error(e->rhs->range.start,
               "cannot access local member from outside its class");
  } else if (m && m->is_protected) {
    diag.Error(e->rhs->range.start,
               "cannot access protected member from outside "
               "its class hierarchy");
  }
}

// 18.11: naming a property in randomize()'s inline argument list changes that
// property's random mode. The random mode of a local or protected member may
// only be changed where the caller can reach that member. When randomize() is
// invoked through an external class handle, its arguments name members of that
// handle's class, so the same visibility rule that governs an obj.member access
// applies to each argument here.
static void CheckRandomizeArgVisibility(
    const Expr* e,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  const Expr* recv = e->lhs;
  if (!recv || recv->kind != ExprKind::kMemberAccess || !recv->lhs ||
      !recv->rhs)
    return;
  if (recv->rhs->kind != ExprKind::kIdentifier ||
      recv->rhs->text != "randomize")
    return;
  if (recv->lhs->kind != ExprKind::kIdentifier) return;
  auto it = var_types.find(recv->lhs->text);
  if (it == var_types.end()) return;
  const auto* cls = FindClassDecl(it->second, unit);
  if (!cls) return;
  for (const auto* arg : e->args) {
    if (!arg || arg->kind != ExprKind::kIdentifier) continue;
    const auto* m = FindMemberInClass(cls, arg->text, unit);
    if (m && m->is_local) {
      diag.Error(arg->range.start,
                 "cannot change random mode of local member from outside "
                 "its class");
    } else if (m && m->is_protected) {
      diag.Error(arg->range.start,
                 "cannot change random mode of protected member from "
                 "outside its class hierarchy");
    }
  }
}

static void CheckVisibilityExpr(
    const Expr* e,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->lhs && e->rhs) {
    CheckMemberAccessVisibility(e, var_types, unit, diag);
  }
  if (e->kind == ExprKind::kCall) {
    CheckRandomizeArgVisibility(e, var_types, unit, diag);
  }
  CheckVisibilityExpr(e->lhs, var_types, unit, diag);
  CheckVisibilityExpr(e->rhs, var_types, unit, diag);
  CheckVisibilityExpr(e->base, var_types, unit, diag);
  CheckVisibilityExpr(e->index, var_types, unit, diag);
  CheckVisibilityExpr(e->condition, var_types, unit, diag);
  CheckVisibilityExpr(e->true_expr, var_types, unit, diag);
  CheckVisibilityExpr(e->false_expr, var_types, unit, diag);
  for (const auto* arg : e->args)
    CheckVisibilityExpr(arg, var_types, unit, diag);
}

static void WalkStmtsForVisibility(
    const Stmt* s,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (!s) return;
  CheckVisibilityExpr(s->lhs, var_types, unit, diag);
  CheckVisibilityExpr(s->rhs, var_types, unit, diag);
  CheckVisibilityExpr(s->expr, var_types, unit, diag);
  CheckVisibilityExpr(s->condition, var_types, unit, diag);
  for (auto* sub : s->stmts) WalkStmtsForVisibility(sub, var_types, unit, diag);
  WalkStmtsForVisibility(s->then_branch, var_types, unit, diag);
  WalkStmtsForVisibility(s->else_branch, var_types, unit, diag);
  WalkStmtsForVisibility(s->body, var_types, unit, diag);
  WalkStmtsForVisibility(s->for_body, var_types, unit, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForVisibility(ci.body, var_types, unit, diag);
}

void Elaborator::ValidateLocalProtectedAccess(const ModuleDecl* decl) {
  if (class_var_types_.empty()) return;
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForVisibility(item->body, class_var_types_, unit_, diag_);
    }
  }
}

static void WalkStmtsForConstClassProp(
    const Stmt* s,
    const std::unordered_set<std::string_view>& global_consts,
    const std::unordered_set<std::string_view>& instance_consts,
    bool in_constructor, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    if (s->lhs && s->lhs->kind == ExprKind::kIdentifier) {
      if (global_consts.count(s->lhs->text)) {
        diag.Error(s->range.start,
                   std::format("assignment to global constant '{}'",
                               s->lhs->text));
      } else if (instance_consts.count(s->lhs->text) && !in_constructor) {
        diag.Error(
            s->range.start,
            std::format(
                "assignment to instance constant '{}' outside constructor",
                s->lhs->text));
      }
    }
  }
  for (auto* sub : s->stmts)
    WalkStmtsForConstClassProp(sub, global_consts, instance_consts,
                               in_constructor, diag);
  WalkStmtsForConstClassProp(s->then_branch, global_consts, instance_consts,
                             in_constructor, diag);
  WalkStmtsForConstClassProp(s->else_branch, global_consts, instance_consts,
                             in_constructor, diag);
  WalkStmtsForConstClassProp(s->body, global_consts, instance_consts,
                             in_constructor, diag);
  WalkStmtsForConstClassProp(s->for_body, global_consts, instance_consts,
                             in_constructor, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForConstClassProp(ci.body, global_consts, instance_consts,
                               in_constructor, diag);
}

void Elaborator::ValidateConstClassProperties() {
  for (const auto* cls : unit_->classes) {
    std::unordered_set<std::string_view> global_consts;
    std::unordered_set<std::string_view> instance_consts;
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kProperty || !m->is_const) continue;
      if (!m->init_expr && m->is_static) {
        diag_.Error(m->loc, "instance constant cannot be declared static");
      }
      if (m->init_expr) {
        global_consts.insert(m->name);
      } else {
        instance_consts.insert(m->name);
      }
    }
    if (global_consts.empty() && instance_consts.empty()) continue;
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
      if (!m->method->body) continue;
      bool is_ctor = m->method->name == "new";
      WalkStmtsForConstClassProp(m->method->body, global_consts,
                                 instance_consts, is_ctor, diag_);
    }
  }
}

static const ClassMember* FindBaseVirtualMethod(const ClassDecl* cls,
                                                std::string_view method_name,
                                                const CompilationUnit* unit) {
  if (cls->base_class.empty()) return nullptr;
  for (const auto* c = FindClassDecl(cls->base_class, unit); c;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kMethod && m->method &&
          m->method->name == method_name &&
          (m->is_virtual || m->is_pure_virtual)) {
        return m;
      }
    }
  }
  return nullptr;
}

static const ClassMember* FindBaseFinalMethod(const ClassDecl* cls,
                                              std::string_view method_name,
                                              const CompilationUnit* unit) {
  if (cls->base_class.empty()) return nullptr;
  for (const auto* c = FindClassDecl(cls->base_class, unit); c;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kMethod && m->method &&
          m->method->name == method_name && m->method->is_method_final) {
        return m;
      }
    }
  }
  return nullptr;
}

static void ValidateOverrideSignature(const ModuleItem* base_method,
                                      const ModuleItem* override_method,
                                      const CompilationUnit* unit,
                                      DiagEngine& diag) {
  const auto& base_args = base_method->func_args;
  const auto& over_args = override_method->func_args;
  if (base_args.size() != over_args.size()) {
    diag.Error(override_method->loc,
               "virtual method override has different number of arguments");
    return;
  }
  for (size_t i = 0; i < base_args.size(); ++i) {
    if (!TypesMatch(base_args[i].data_type, over_args[i].data_type)) {
      diag.Error(override_method->loc,
                 std::format("virtual method override argument '{}' has "
                             "mismatched type",
                             over_args[i].name));
    }
    if (base_args[i].name != over_args[i].name) {
      diag.Error(override_method->loc,
                 std::format("virtual method override argument name '{}' "
                             "does not match base '{}' ",
                             over_args[i].name, base_args[i].name));
    }
    if (base_args[i].direction != over_args[i].direction) {
      diag.Error(override_method->loc,
                 std::format("virtual method override argument '{}' has "
                             "mismatched direction",
                             over_args[i].name));
    }
    bool base_has_default = base_args[i].default_value != nullptr;
    bool over_has_default = over_args[i].default_value != nullptr;
    if (base_has_default != over_has_default) {
      diag.Error(override_method->loc,
                 std::format("virtual method override argument '{}': "
                             "presence of default must match",
                             over_args[i].name));
    }
  }
  if (!TypesMatch(base_method->return_type, override_method->return_type)) {
    if (base_method->return_type.kind == DataTypeKind::kNamed &&
        override_method->return_type.kind == DataTypeKind::kNamed &&
        IsClassDerivedFrom(override_method->return_type.type_name,
                           base_method->return_type.type_name, unit)) {
      return;
    }
    diag.Error(override_method->loc,
               "virtual method override has mismatched return type");
  }
}

void Elaborator::ValidateOneMethodOverride(const ClassDecl* cls,
                                           const ClassMember* m) {
  auto* method = m->method;
  if (method->is_method_initial && method->is_method_extends) {
    diag_.Error(method->loc,
                "':initial' and ':extends' are mutually exclusive");
    return;
  }
  const auto* base_virtual = FindBaseVirtualMethod(cls, method->name, unit_);
  if (method->is_method_initial && base_virtual) {
    diag_.Error(method->loc,
                "method with ':initial' shall not override a virtual "
                "base class method");
  }
  if (method->is_method_extends && !base_virtual) {
    diag_.Error(method->loc,
                "method with ':extends' does not override a virtual "
                "base class method");
  }

  const auto* base_final = FindBaseFinalMethod(cls, method->name, unit_);
  if (base_final) {
    diag_.Error(method->loc, "cannot override a method declared ':final'");
  }

  if (base_virtual && base_virtual->method) {
    ValidateOverrideSignature(base_virtual->method, method, unit_, diag_);
  }
}

void Elaborator::ValidateVirtualMethodOverrides() {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
      ValidateOneMethodOverride(cls, m);
    }
  }
}

static void CollectPureVirtualMethods(
    const ClassDecl* cls, const CompilationUnit* unit,
    std::vector<std::string_view>& pure_names) {
  if (!cls) return;
  if (!cls->base_class.empty()) {
    const auto* base = FindClassDecl(cls->base_class, unit);
    CollectPureVirtualMethods(base, unit, pure_names);
  }
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
    if (m->is_pure_virtual) {
      pure_names.push_back(m->method->name);
    } else if (m->is_virtual) {
      std::erase(pure_names, m->method->name);
    }
  }
}

void Elaborator::ValidateAbstractClassUnimplemented(const ClassDecl* cls) {
  if (cls->is_virtual || cls->base_class.empty()) return;
  std::vector<std::string_view> unimpl;
  CollectPureVirtualMethods(cls, unit_, unimpl);
  for (auto name : unimpl) {
    diag_.Error(cls->range.start,
                std::format("non-abstract class '{}' does not implement "
                            "pure virtual method '{}'",
                            cls->name, name));
  }
}

void Elaborator::ValidateAbstractClassRules() {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      if (m->kind == ClassMemberKind::kMethod && m->method) {
        if (m->is_pure_virtual && m->method->is_method_final) {
          diag_.Error(
              m->method->loc,
              "':final' shall not be specified on a pure virtual method");
        }
      } else if (m->kind == ClassMemberKind::kConstraint) {
        if (m->is_pure_virtual && m->is_constraint_final) {
          diag_.Error(
              m->loc,
              "':final' shall not be specified on a pure constraint");
        }
      }
    }
    ValidateAbstractClassUnimplemented(cls);
  }
}

static const ModuleItem* FindExternPrototype(const ClassDecl* cls,
                                              std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == name && m->method->is_extern) {
      return m->method;
    }
  }
  return nullptr;
}

// §8.24: when an out-of-block declaration repeats a default argument value, it
// shall be syntactically identical to the one in the prototype. The default
// values are parsed into expression trees, so compare those trees node by node
// as a faithful stand-in for syntactic identity.
static bool DefaultArgExprsEqual(const Expr* a, const Expr* b) {
  if (a == nullptr || b == nullptr) return a == b;
  if (a->kind != b->kind || a->op != b->op || a->text != b->text ||
      a->scope_prefix != b->scope_prefix || a->callee != b->callee ||
      a->int_val != b->int_val || a->real_val != b->real_val ||
      a->is_parenthesized != b->is_parenthesized) {
    return false;
  }
  if (!DefaultArgExprsEqual(a->lhs, b->lhs) ||
      !DefaultArgExprsEqual(a->rhs, b->rhs) ||
      !DefaultArgExprsEqual(a->condition, b->condition) ||
      !DefaultArgExprsEqual(a->true_expr, b->true_expr) ||
      !DefaultArgExprsEqual(a->false_expr, b->false_expr) ||
      !DefaultArgExprsEqual(a->base, b->base) ||
      !DefaultArgExprsEqual(a->index, b->index)) {
    return false;
  }
  if (a->args.size() != b->args.size()) return false;
  for (size_t i = 0; i < a->args.size(); ++i) {
    if (!DefaultArgExprsEqual(a->args[i], b->args[i])) return false;
  }
  return true;
}

static void ValidateOutOfBlockSignature(const ModuleItem* proto,
                                        const ModuleItem* impl,
                                        std::string_view class_name,
                                        DiagEngine& diag) {
  if (proto->kind != impl->kind) {
    diag.Error(impl->loc,
               std::format("out-of-block declaration for '{}::{}' is a {} but "
                           "the prototype is a {}",
                           class_name, impl->name,
                           impl->kind == ModuleItemKind::kFunctionDecl
                               ? "function"
                               : "task",
                           proto->kind == ModuleItemKind::kFunctionDecl
                               ? "function"
                               : "task"));
    return;
  }
  const auto& proto_args = proto->func_args;
  const auto& impl_args = impl->func_args;
  if (proto_args.size() != impl_args.size()) {
    diag.Error(impl->loc,
               std::format("out-of-block declaration for '{}::{}' has {} "
                           "argument(s) but the prototype has {}",
                           class_name, impl->name, impl_args.size(),
                           proto_args.size()));
    return;
  }
  for (size_t i = 0; i < proto_args.size(); ++i) {
    if (!TypesMatch(proto_args[i].data_type, impl_args[i].data_type)) {
      diag.Error(impl->loc,
                 std::format("out-of-block declaration for '{}::{}' argument "
                             "'{}' has mismatched type",
                             class_name, impl->name, impl_args[i].name));
    }
    if (proto_args[i].direction != impl_args[i].direction) {
      diag.Error(impl->loc,
                 std::format("out-of-block declaration for '{}::{}' argument "
                             "'{}' has mismatched direction",
                             class_name, impl->name, impl_args[i].name));
    }
    // §8.24: omitting the prototype's default value is allowed, but repeating a
    // default value in the out-of-block declaration requires a syntactically
    // identical default value in the prototype.
    const Expr* impl_default = impl_args[i].default_value;
    if (impl_default != nullptr &&
        !DefaultArgExprsEqual(proto_args[i].default_value, impl_default)) {
      diag.Error(impl->loc,
                 std::format("out-of-block declaration for '{}::{}' argument "
                             "'{}' has a default value that is not "
                             "syntactically identical to the prototype",
                             class_name, impl->name, impl_args[i].name));
    }
  }
  if (proto->kind == ModuleItemKind::kFunctionDecl) {
    auto impl_ret = impl->return_type;
    if (impl_ret.kind == DataTypeKind::kNamed && !impl_ret.scope_name.empty() &&
        impl_ret.scope_name == class_name) {
      impl_ret.scope_name = {};
    }
    if (!TypesMatch(proto->return_type, impl_ret)) {
      diag.Error(impl->loc,
                 std::format("out-of-block declaration for '{}::{}' has "
                             "mismatched return type",
                             class_name, impl->name));
    }
  }
}

static const ModuleDecl* FindInterfaceDecl(std::string_view name,
                                           const CompilationUnit* unit) {
  for (const auto* ifc : unit->interfaces) {
    if (ifc->name == name) return ifc;
  }
  return nullptr;
}

static const ModuleItem* FindInterfaceExternPrototype(const ModuleDecl* ifc,
                                                      std::string_view name) {
  for (const auto* it : ifc->items) {
    if ((it->kind == ModuleItemKind::kFunctionDecl ||
         it->kind == ModuleItemKind::kTaskDecl) &&
        it->is_extern && it->name == name) {
      return it;
    }
  }
  return nullptr;
}

// True when location a strictly precedes location b within the same source
// file. Locations from different files carry no relative order, so they are
// reported as not-preceding to avoid spurious diagnostics.
static bool LocPrecedes(const SourceLoc& a, const SourceLoc& b) {
  if (a.file_id != b.file_id) return false;
  if (a.line != b.line) return a.line < b.line;
  return a.column < b.column;
}

void Elaborator::ValidateOutOfBlockDeclarations() {
  std::unordered_set<std::string> linked;
  for (auto* item : unit_->cu_items) {
    if (item->method_class.empty()) continue;
    bool is_func = (item->kind == ModuleItemKind::kFunctionDecl);
    bool is_task = (item->kind == ModuleItemKind::kTaskDecl);
    if (!is_func && !is_task) continue;
    const auto* cls = FindClassDecl(item->method_class, unit_);
    if (!cls) {
      const auto* ifc = FindInterfaceDecl(item->method_class, unit_);
      if (ifc) {
        const auto* proto = FindInterfaceExternPrototype(ifc, item->name);
        if (!proto) {
          diag_.Error(
              item->loc,
              std::format("no matching extern prototype for '{}.{}' in "
                          "interface '{}'",
                          item->method_class, item->name, item->method_class));
          continue;
        }
        auto key =
            std::string(item->method_class) + "." + std::string(item->name);
        if (linked.count(key)) {
          diag_.Error(
              item->loc,
              std::format("duplicate hierarchical body for '{}.{}'",
                          item->method_class, item->name));
          continue;
        }
        linked.insert(key);
        ValidateOutOfBlockSignature(proto, item, item->method_class, diag_);
        continue;
      }
      diag_.Error(item->loc,
                  std::format("out-of-block declaration for unknown class '{}'",
                              item->method_class));
      continue;
    }
    const auto* proto = FindExternPrototype(cls, item->name);
    if (!proto) {
      diag_.Error(
          item->loc,
          std::format("no matching extern prototype for '{}::{}' in "
                      "class '{}'",
                      item->method_class, item->name, item->method_class));
      continue;
    }
    // §8.24: an out-of-block declaration shall follow the class declaration, so
    // a body that appears ahead of its class in source order is illegal.
    if (LocPrecedes(item->loc, cls->range.start)) {
      diag_.Error(
          item->loc,
          std::format("out-of-block declaration for '{}::{}' shall follow the "
                      "declaration of class '{}'",
                      item->method_class, item->name, item->method_class));
      continue;
    }
    auto key = std::string(item->method_class) + "::" + std::string(item->name);
    if (linked.count(key)) {
      diag_.Error(item->loc,
                  std::format("duplicate out-of-block declaration for '{}::{}'",
                              item->method_class, item->name));
      continue;
    }
    linked.insert(key);
    ValidateOutOfBlockSignature(proto, item, item->method_class, diag_);
  }
}

void Elaborator::ValidateInterfaceClassMembers(const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        (m->method->is_method_initial || m->method->is_method_extends ||
         m->method->is_method_final)) {
      diag_.Error(m->method->loc,
                  "dynamic_override_specifiers shall not be used in "
                  "an interface class");
    }
    if (m->kind == ClassMemberKind::kMethod && !m->is_pure_virtual) {
      diag_.Error(m->method ? m->method->loc : cls->range.start,
                  std::format("interface class '{}' shall only contain "
                              "pure virtual methods",
                              cls->name));
    } else if (m->kind == ClassMemberKind::kProperty && !m->is_const) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' shall not contain "
                              "data members",
                              cls->name));
    } else if (m->kind == ClassMemberKind::kConstraint) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' shall not contain "
                              "constraint blocks",
                              cls->name));
    } else if (m->kind == ClassMemberKind::kCovergroup) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' shall not contain "
                              "covergroups",
                              cls->name));
    } else if (m->kind == ClassMemberKind::kClassDecl) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' shall not contain "
                              "nested classes",
                              cls->name));
    }

    if (m->kind == ClassMemberKind::kMethod && m->method) {
      for (const auto& arg : m->method->func_args) {
        if (arg.default_value &&
            !IsConstantExpr(arg.default_value, cu_param_scope_)) {
          diag_.Error(m->method->loc,
                      std::format("interface class method '{}' argument '{}': "
                                  "default value must be a constant expression",
                                  m->method->name, arg.name));
        }
      }
    }
  }
}

static bool IsForwardTypedefOnly(std::string_view name,
                                 const ClassDecl* before_cls,
                                 const CompilationUnit* unit) {
  bool has_forward = false;
  for (const auto* item : unit->cu_items) {
    if (item->kind == ModuleItemKind::kTypedef && item->name == name &&
        item->typedef_type.kind == DataTypeKind::kImplicit) {
      has_forward = true;
    }
  }
  if (!has_forward) return false;
  for (const auto* c : unit->classes) {
    if (c == before_cls) return true;
    if (c->name == name) return false;
  }
  return true;
}

static bool IsDeclaredBefore(std::string_view name,
                             const ClassDecl* before_cls,
                             const CompilationUnit* unit) {
  for (const auto* c : unit->classes) {
    if (c == before_cls) return false;
    if (c->name == name) return true;
  }
  return false;
}

void Elaborator::ValidateInterfaceClassInheritance(const ClassDecl* cls) {
  if (!cls->implements_types.empty()) {
    diag_.Error(cls->range.start,
                std::format("interface class '{}' shall not use "
                            "'implements'",
                            cls->name));
  }
  if (cls->base_class.empty()) return;

  if (cls->type_param_names.count(cls->base_class) > 0) {
    diag_.Error(cls->range.start,
                std::format("interface class '{}' shall not extend type "
                            "parameter '{}'",
                            cls->name, cls->base_class));
  } else if (IsForwardTypedefOnly(cls->base_class, cls, unit_)) {

    diag_.Error(cls->range.start,
                std::format("interface class '{}' shall not extend forward "
                            "typedef '{}'; the interface class must be "
                            "declared before it is extended",
                            cls->name, cls->base_class));
  } else if (!IsDeclaredBefore(cls->base_class, cls, unit_)) {

    const auto* base = FindClassDecl(cls->base_class, unit_);
    if (base && base->is_interface) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' must be declared before "
                              "it is extended by '{}'",
                              cls->base_class, cls->name));
    }
  }

  const auto* base = FindClassDecl(cls->base_class, unit_);
  if (base && !base->is_interface) {
    diag_.Error(cls->range.start,
                std::format("interface class '{}' cannot extend "
                            "non-interface class '{}'",
                            cls->name, cls->base_class));
  }
  for (const auto& ref : cls->extends_interfaces) {
    auto iface_name = ref.name;

    if (cls->type_param_names.count(iface_name) > 0) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' shall not extend type "
                              "parameter '{}'",
                              cls->name, iface_name));
      continue;
    }

    if (IsForwardTypedefOnly(iface_name, cls, unit_)) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' shall not extend forward "
                              "typedef '{}'; the interface class must be "
                              "declared before it is extended",
                              cls->name, iface_name));
      continue;
    }

    if (!IsDeclaredBefore(iface_name, cls, unit_)) {
      const auto* ibase = FindClassDecl(iface_name, unit_);
      if (ibase && ibase->is_interface) {
        diag_.Error(cls->range.start,
                    std::format("interface class '{}' must be declared before "
                                "it is extended by '{}'",
                                iface_name, cls->name));
        continue;
      }
    }
    const auto* ibase = FindClassDecl(iface_name, unit_);
    if (ibase && !ibase->is_interface) {
      diag_.Error(cls->range.start,
                  std::format("interface class '{}' cannot extend "
                              "non-interface class '{}'",
                              cls->name, iface_name));
    }
  }
}

void Elaborator::ValidateRegularClassInheritance(const ClassDecl* cls) {
  if (!cls->base_class.empty()) {
    const auto* base = FindClassDecl(cls->base_class, unit_);
    if (base && base->is_interface) {
      diag_.Error(cls->range.start,
                  std::format("class '{}' cannot extend interface class "
                              "'{}'; use 'implements' instead",
                              cls->name, cls->base_class));
    }
  }
  for (const auto& ref : cls->implements_types) {
    auto impl_name = ref.name;

    if (cls->type_param_names.count(impl_name) > 0) {
      diag_.Error(cls->range.start,
                  std::format("class '{}' shall not implement type "
                              "parameter '{}'",
                              cls->name, impl_name));
      continue;
    }

    if (IsForwardTypedefOnly(impl_name, cls, unit_)) {
      diag_.Error(cls->range.start,
                  std::format("class '{}' shall not implement forward "
                              "typedef '{}'; the interface class must be "
                              "declared before it is implemented",
                              cls->name, impl_name));
      continue;
    }

    if (!IsDeclaredBefore(impl_name, cls, unit_)) {
      const auto* impl = FindClassDecl(impl_name, unit_);
      if (impl && impl->is_interface) {
        diag_.Error(cls->range.start,
                    std::format("interface class '{}' must be declared before "
                                "it is implemented by '{}'",
                                impl_name, cls->name));
        continue;
      }
    }
    const auto* impl = FindClassDecl(impl_name, unit_);
    if (impl && !impl->is_interface) {
      diag_.Error(cls->range.start,
                  std::format("class '{}' cannot implement non-interface "
                              "class '{}'",
                              cls->name, impl_name));
    }
  }
}

static bool MethodSignaturesCompatible(const ModuleItem* a,
                                       const ModuleItem* b) {
  if (!TypesMatch(a->return_type, b->return_type)) return false;
  if (a->func_args.size() != b->func_args.size()) return false;
  for (size_t i = 0; i < a->func_args.size(); ++i) {
    if (!TypesMatch(a->func_args[i].data_type, b->func_args[i].data_type))
      return false;
    if (a->func_args[i].direction != b->func_args[i].direction) return false;
  }
  return true;
}

static std::string MakeSpecKey(std::string_view name,
                               const std::vector<DataType>& type_params) {
  if (type_params.empty()) return std::string(name);
  std::string key(name);
  key += "#(";
  for (size_t i = 0; i < type_params.size(); ++i) {
    if (i > 0) key += ',';
    const auto& dt = type_params[i];
    if (!dt.type_name.empty())
      key += dt.type_name;
    else
      key += std::to_string(static_cast<int>(dt.kind));
  }
  key += ')';
  return key;
}

using IfaceMethodMap =
    std::unordered_map<std::string_view,
                       std::vector<std::pair<std::string,
                                             const ModuleItem*>>>;

static void CollectInterfacePureVirtualMethods(
    const ClassDecl* iface, const std::string& spec_key,
    const CompilationUnit* unit, IfaceMethodMap& out,
    std::unordered_set<std::string>& visited) {
  if (!visited.insert(spec_key).second) return;
  for (const auto* m : iface->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->is_pure_virtual) continue;
    if (!m->method) continue;
    out[m->method->name].push_back({spec_key, m->method});
  }
  if (!iface->base_class.empty()) {
    const auto* base = FindClassDecl(iface->base_class, unit);
    if (base && base->is_interface) {
      auto base_key = MakeSpecKey(iface->base_class,
                                  iface->base_class_type_params);
      CollectInterfacePureVirtualMethods(base, base_key, unit, out, visited);
    }
  }
  for (const auto& ref : iface->extends_interfaces) {
    const auto* ext = FindClassDecl(ref.name, unit);
    if (ext && ext->is_interface) {
      auto ext_key = MakeSpecKey(ref.name, ref.type_params);
      CollectInterfacePureVirtualMethods(ext, ext_key, unit, out, visited);
    }
  }
}

static void CollectImplementedInterfaces(
    const ClassDecl* cls, const CompilationUnit* unit,
    std::vector<InterfaceRef>& out) {
  for (const auto& iface : cls->implements_types) {
    out.push_back(iface);
  }
  if (!cls->base_class.empty()) {
    const auto* base = FindClassDecl(cls->base_class, unit);
    if (base && !base->is_interface) {
      CollectImplementedInterfaces(base, unit, out);
    }
  }
}

static void ValidateMethodNameConflicts(
    const ClassDecl* cls, const CompilationUnit* unit, DiagEngine& diag) {
  IfaceMethodMap iface_methods;
  std::unordered_set<std::string> visited;

  if (cls->is_interface) {

    if (!cls->base_class.empty()) {
      const auto* base = FindClassDecl(cls->base_class, unit);
      if (base && base->is_interface) {
        auto base_key = MakeSpecKey(cls->base_class,
                                    cls->base_class_type_params);
        CollectInterfacePureVirtualMethods(base, base_key, unit,
                                           iface_methods, visited);
      }
    }
    for (const auto& ref : cls->extends_interfaces) {
      const auto* ext = FindClassDecl(ref.name, unit);
      if (ext && ext->is_interface) {
        auto ext_key = MakeSpecKey(ref.name, ref.type_params);
        CollectInterfacePureVirtualMethods(ext, ext_key, unit, iface_methods,
                                           visited);
      }
    }
  } else {

    std::vector<InterfaceRef> all_ifaces;
    CollectImplementedInterfaces(cls, unit, all_ifaces);
    std::unordered_set<std::string> seen_iface;
    for (const auto& iref : all_ifaces) {
      auto iface_key = MakeSpecKey(iref.name, iref.type_params);
      if (!seen_iface.insert(iface_key).second) continue;
      const auto* iface = FindClassDecl(iref.name, unit);
      if (!iface || !iface->is_interface) continue;
      CollectInterfacePureVirtualMethods(iface, iface_key, unit,
                                         iface_methods, visited);
    }
  }

  for (const auto& [method_name, entries] : iface_methods) {
    if (entries.size() < 2) continue;
    if (method_name == "pre_randomize" || method_name == "post_randomize")
      continue;
    const auto* first_method = entries[0].second;
    for (size_t i = 1; i < entries.size(); ++i) {
      if (!MethodSignaturesCompatible(first_method, entries[i].second)) {
        diag.Error(
            cls->range.start,
            std::format("method name conflict for '{}' in '{}': incompatible "
                        "signatures in interface '{}' and interface '{}'",
                        method_name, cls->name, entries[0].first,
                        entries[i].first));
        break;
      }
    }
  }

  if (!cls->is_interface) {
    for (const auto& [method_name, entries] : iface_methods) {

      const ModuleItem* impl = nullptr;
      for (const auto* cm : cls->members) {
        if (cm->kind == ClassMemberKind::kMethod && cm->method &&
            cm->method->name == method_name &&
            (cm->is_virtual || cm->is_pure_virtual)) {
          impl = cm->method;
          break;
        }
      }
      if (!impl) {
        for (const auto* walk = cls->base_class.empty()
                                    ? nullptr
                                    : FindClassDecl(cls->base_class, unit);
             walk; walk = walk->base_class.empty()
                              ? nullptr
                              : FindClassDecl(walk->base_class, unit)) {
          for (const auto* bm : walk->members) {
            if (bm->kind == ClassMemberKind::kMethod && bm->method &&
                bm->method->name == method_name && bm->is_virtual) {
              impl = bm->method;
              break;
            }
          }
          if (impl) break;
        }
      }
      if (!impl) continue;
      for (const auto& [iface_name, iface_method] : entries) {
        if (!MethodSignaturesCompatible(impl, iface_method)) {
          diag.Error(
              impl->loc,
              std::format("method '{}' does not match signature of pure "
                          "virtual method '{}' in interface '{}'",
                          method_name, method_name, iface_name));
          break;
        }
      }
    }
  }
}

static bool HasConcreteVirtualMethodInHierarchy(const ClassDecl* cls,
                                                std::string_view method_name,
                                                const CompilationUnit* unit) {
  for (const auto* cm : cls->members) {
    if (cm->kind == ClassMemberKind::kMethod && cm->method &&
        cm->method->name == method_name && cm->is_virtual) {
      return true;
    }
  }
  if (cls->base_class.empty()) return false;
  const auto* walk = FindClassDecl(cls->base_class, unit);
  while (walk) {
    for (const auto* bm : walk->members) {
      if (bm->kind == ClassMemberKind::kMethod && bm->method &&
          bm->method->name == method_name && bm->is_virtual &&
          !bm->is_pure_virtual) {
        return true;
      }
    }
    walk = walk->base_class.empty() ? nullptr
                                    : FindClassDecl(walk->base_class, unit);
  }
  return false;
}

static const ModuleItem* FindConcreteMethodInHierarchy(
    const ClassDecl* cls, std::string_view method_name,
    const CompilationUnit* unit) {
  for (const auto* cm : cls->members) {
    if (cm->kind == ClassMemberKind::kMethod && cm->method &&
        cm->method->name == method_name && cm->is_virtual) {
      return cm->method;
    }
  }
  const auto* walk = cls->base_class.empty()
                         ? nullptr
                         : FindClassDecl(cls->base_class, unit);
  while (walk) {
    for (const auto* bm : walk->members) {
      if (bm->kind == ClassMemberKind::kMethod && bm->method &&
          bm->method->name == method_name && bm->is_virtual &&
          !bm->is_pure_virtual) {
        return bm->method;
      }
    }
    walk = walk->base_class.empty() ? nullptr
                                    : FindClassDecl(walk->base_class, unit);
  }
  return nullptr;
}

static void CheckInterfaceMethods(const ClassDecl* cls, const ClassDecl* iface,
                                  std::string_view iface_name,
                                  const CompilationUnit* unit,
                                  DiagEngine& diag) {
  for (const auto* im : iface->members) {
    if (im->kind != ClassMemberKind::kMethod || !im->is_pure_virtual) continue;
    if (!im->method) continue;
    const auto* impl = FindConcreteMethodInHierarchy(cls, im->method->name,
                                                     unit);
    if (!impl) {
      diag.Error(cls->range.start,
                 std::format("class '{}' does not implement pure virtual "
                             "method '{}' from interface '{}'",
                             cls->name, im->method->name, iface_name));
      continue;
    }

    const auto& iface_args = im->method->func_args;
    const auto& impl_args = impl->func_args;
    size_t n = std::min(iface_args.size(), impl_args.size());
    for (size_t i = 0; i < n; ++i) {
      bool iface_has = iface_args[i].default_value != nullptr;
      bool impl_has = impl_args[i].default_value != nullptr;
      // §8.26.8: the default argument value of an interface class method must
      // be the same for every class that implements it. A default present on
      // one side but absent on the other cannot yield a common value, so the
      // implementing method's defaults must mirror the interface prototype's.
      if (iface_has != impl_has) {
        diag.Error(impl->loc,
                   std::format("method '{}' argument '{}': default value "
                               "presence does not match interface '{}'",
                               impl->name, impl_args[i].name, iface_name));
        continue;
      }
      if (!iface_has) continue;
      auto iface_val = ConstEvalInt(iface_args[i].default_value);
      auto impl_val = ConstEvalInt(impl_args[i].default_value);
      if (iface_val && impl_val && *iface_val != *impl_val) {
        diag.Error(impl->loc,
                   std::format("method '{}' argument '{}': default value "
                               "does not match interface '{}' (expected {}, "
                               "got {})",
                               impl->name, impl_args[i].name, iface_name,
                               *iface_val, *impl_val));
      }
    }
  }
}

void Elaborator::ValidateImplementsInterfaceMethods(const ClassDecl* cls) {
  if (cls->is_virtual) return;
  std::vector<InterfaceRef> all_ifaces;
  CollectImplementedInterfaces(cls, unit_, all_ifaces);
  if (all_ifaces.empty()) return;
  std::unordered_set<std::string> seen;
  for (const auto& iref : all_ifaces) {
    auto iface_key = MakeSpecKey(iref.name, iref.type_params);
    if (!seen.insert(iface_key).second) continue;
    const auto* iface = FindClassDecl(iref.name, unit_);
    if (!iface) continue;
    CheckInterfaceMethods(cls, iface, iref.name, unit_, diag_);
  }
}

using NameOriginMap =
    std::unordered_map<std::string_view,
                       std::unordered_set<std::string>>;

static void CollectOwnParamTypeNames(
    const ClassDecl* iface,
    std::unordered_set<std::string_view>& own_names) {
  for (const auto& [pname, _] : iface->params)
    own_names.insert(pname);
  for (const auto* m : iface->members) {
    if (m->kind == ClassMemberKind::kTypedef)
      own_names.insert(m->name);
    else if (m->kind == ClassMemberKind::kProperty)
      own_names.insert(m->name);
  }
}

static void CollectEffectiveParamTypeNames(
    const ClassDecl* iface, const std::string& spec_key,
    const CompilationUnit* unit, NameOriginMap& out) {
  std::unordered_set<std::string_view> own_names;
  CollectOwnParamTypeNames(iface, own_names);
  for (auto n : own_names)
    out[n].insert(spec_key);
  auto inherit = [&](const ClassDecl* parent, const std::string& parent_key) {
    NameOriginMap parent_map;
    CollectEffectiveParamTypeNames(parent, parent_key, unit, parent_map);
    for (const auto& [name, origins] : parent_map) {
      if (own_names.count(name)) continue;
      for (const auto& o : origins) out[name].insert(o);
    }
  };
  if (!iface->base_class.empty()) {
    const auto* base = FindClassDecl(iface->base_class, unit);
    if (base && base->is_interface) {
      auto base_key = MakeSpecKey(iface->base_class,
                                  iface->base_class_type_params);
      inherit(base, base_key);
    }
  }
  for (const auto& ref : iface->extends_interfaces) {
    const auto* ext = FindClassDecl(ref.name, unit);
    if (ext && ext->is_interface) {
      auto ext_key = MakeSpecKey(ref.name, ref.type_params);
      inherit(ext, ext_key);
    }
  }
}

static void ValidateParamTypeConflicts(
    const ClassDecl* cls, const CompilationUnit* unit, DiagEngine& diag) {
  if (!cls->is_interface) return;
  std::unordered_set<std::string_view> own_names;
  CollectOwnParamTypeNames(cls, own_names);
  NameOriginMap inherited;
  auto process = [&](const ClassDecl* parent, const std::string& parent_key) {
    NameOriginMap parent_map;
    CollectEffectiveParamTypeNames(parent, parent_key, unit, parent_map);
    for (const auto& [name, origins] : parent_map) {
      if (own_names.count(name)) continue;
      for (const auto& o : origins) inherited[name].insert(o);
    }
  };
  if (!cls->base_class.empty()) {
    const auto* base = FindClassDecl(cls->base_class, unit);
    if (base && base->is_interface) {
      auto base_key = MakeSpecKey(cls->base_class,
                                  cls->base_class_type_params);
      process(base, base_key);
    }
  }
  for (const auto& ref : cls->extends_interfaces) {
    const auto* ext = FindClassDecl(ref.name, unit);
    if (ext && ext->is_interface) {
      auto ext_key = MakeSpecKey(ref.name, ref.type_params);
      process(ext, ext_key);
    }
  }
  for (const auto& [name, origins] : inherited) {
    if (origins.size() > 1) {
      diag.Error(
          cls->range.start,
          std::format("parameter or type '{}' in interface class '{}' is "
                      "inherited from multiple interface classes and must be "
                      "overridden",
                      name, cls->name));
    }
  }
}

void Elaborator::ValidateInterfaceClassRules() {
  for (const auto* cls : unit_->classes) {
    if (cls->is_interface) {
      ValidateInterfaceClassMembers(cls);
      ValidateInterfaceClassInheritance(cls);
    } else {
      ValidateRegularClassInheritance(cls);
      ValidateImplementsInterfaceMethods(cls);
    }

    ValidateMethodNameConflicts(cls, unit_, diag_);

    ValidateParamTypeConflicts(cls, unit_, diag_);
  }
}

static void CheckParamScopeExpr(
    const Expr* e,
    const std::unordered_set<std::string_view>& param_classes,
    DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->lhs && e->rhs &&
      e->lhs->kind == ExprKind::kIdentifier &&
      !e->lhs->has_param_spec &&
      param_classes.count(e->lhs->text)) {
    diag.Error(e->lhs->range.start,
               std::format("unadorned name '{}' used as scope resolution "
                           "prefix for parameterized class; use explicit "
                           "specialization '{}#(...)::' or '{}#()::'",
                           e->lhs->text, e->lhs->text, e->lhs->text));
  }
  CheckParamScopeExpr(e->lhs, param_classes, diag);
  CheckParamScopeExpr(e->rhs, param_classes, diag);
  CheckParamScopeExpr(e->base, param_classes, diag);
  CheckParamScopeExpr(e->index, param_classes, diag);
  CheckParamScopeExpr(e->condition, param_classes, diag);
  CheckParamScopeExpr(e->true_expr, param_classes, diag);
  CheckParamScopeExpr(e->false_expr, param_classes, diag);
  for (const auto* arg : e->args)
    CheckParamScopeExpr(arg, param_classes, diag);
}

static void WalkStmtsForParamScope(
    const Stmt* s,
    const std::unordered_set<std::string_view>& param_classes,
    DiagEngine& diag) {
  if (!s) return;
  CheckParamScopeExpr(s->lhs, param_classes, diag);
  CheckParamScopeExpr(s->rhs, param_classes, diag);
  CheckParamScopeExpr(s->expr, param_classes, diag);
  CheckParamScopeExpr(s->condition, param_classes, diag);
  for (auto* sub : s->stmts) WalkStmtsForParamScope(sub, param_classes, diag);
  WalkStmtsForParamScope(s->then_branch, param_classes, diag);
  WalkStmtsForParamScope(s->else_branch, param_classes, diag);
  WalkStmtsForParamScope(s->body, param_classes, diag);
  WalkStmtsForParamScope(s->for_body, param_classes, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForParamScope(ci.body, param_classes, diag);
}

void Elaborator::ValidateParameterizedScopeResolution(const ModuleDecl* decl) {
  if (parameterized_class_names_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckParamScopeExpr(item->assign_rhs, parameterized_class_names_, diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForParamScope(item->body, parameterized_class_names_, diag_);
    }
  }
}

// §6.20.3 and §8.23 both state the same restriction: while a type parameter
// may resolve to a class type, using it as the prefix of the class scope
// resolution operator '::' is restricted to typedef declarations, the type
// operator, and type parameter assignments. Those three contexts are parsed as
// data types (carrying a scope_name), never as expressions, so a type
// parameter that surfaces as the prefix of a member-access expression is always
// outside the permitted set. Both subclauses agree on this rule; enforcing it
// from one place keeps them consistent.
static void CheckTypeParamScopeExpr(
    const Expr* e,
    const std::unordered_set<std::string_view>& type_params,
    DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->lhs && e->rhs &&
      e->lhs->kind == ExprKind::kIdentifier &&
      type_params.count(e->lhs->text)) {
    diag.Error(e->lhs->range.start,
               std::format("type parameter '{}' may prefix the class scope "
                           "resolution operator only within a typedef "
                           "declaration, the type operator, or a type "
                           "parameter assignment",
                           e->lhs->text));
  }
  CheckTypeParamScopeExpr(e->lhs, type_params, diag);
  CheckTypeParamScopeExpr(e->rhs, type_params, diag);
  CheckTypeParamScopeExpr(e->base, type_params, diag);
  CheckTypeParamScopeExpr(e->index, type_params, diag);
  CheckTypeParamScopeExpr(e->condition, type_params, diag);
  CheckTypeParamScopeExpr(e->true_expr, type_params, diag);
  CheckTypeParamScopeExpr(e->false_expr, type_params, diag);
  for (const auto* arg : e->args)
    CheckTypeParamScopeExpr(arg, type_params, diag);
}

static void WalkStmtsForTypeParamScope(
    const Stmt* s,
    const std::unordered_set<std::string_view>& type_params,
    DiagEngine& diag) {
  if (!s) return;
  CheckTypeParamScopeExpr(s->lhs, type_params, diag);
  CheckTypeParamScopeExpr(s->rhs, type_params, diag);
  CheckTypeParamScopeExpr(s->expr, type_params, diag);
  CheckTypeParamScopeExpr(s->condition, type_params, diag);
  for (auto* sub : s->stmts) WalkStmtsForTypeParamScope(sub, type_params, diag);
  WalkStmtsForTypeParamScope(s->then_branch, type_params, diag);
  WalkStmtsForTypeParamScope(s->else_branch, type_params, diag);
  WalkStmtsForTypeParamScope(s->body, type_params, diag);
  WalkStmtsForTypeParamScope(s->for_body, type_params, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForTypeParamScope(ci.body, type_params, diag);
}

void Elaborator::ValidateTypeParamScopeUsage(const ModuleDecl* decl) {
  // Type parameters come from the parameter port list (recorded by the parser)
  // and from body declarations, where a `parameter type`/`localparam type`
  // item is carried as a parameter declaration whose data type is void.
  std::unordered_set<std::string_view> type_params = decl->type_param_names;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kParamDecl &&
        item->data_type.kind == DataTypeKind::kVoid) {
      type_params.insert(item->name);
    }
  }
  if (type_params.empty()) return;

  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckTypeParamScopeExpr(item->assign_lhs, type_params, diag_);
      CheckTypeParamScopeExpr(item->assign_rhs, type_params, diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForTypeParamScope(item->body, type_params, diag_);
    }
  }
}

void Elaborator::ValidateTypeParamScopePrefixResolvesToClass(
    const ModuleDecl* decl) {
  // §6.20.3: a type parameter may prefix the class scope resolution operator in
  // an allowed context (such as a typedef declaration) only when it resolves to
  // a class type; it shall be an error if the prefix does not resolve to a
  // class. Collect each body type parameter and the type it is bound to.
  std::unordered_map<std::string_view, const DataType*> type_param_bound;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kParamDecl &&
        item->data_type.kind == DataTypeKind::kVoid &&
        item->typedef_type.kind != DataTypeKind::kImplicit) {
      type_param_bound[item->name] = &item->typedef_type;
    }
  }
  if (type_param_bound.empty()) return;

  // Returns true when the bound type is definitely not a class. A built-in or
  // otherwise non-named type can never be a class; a named type is left alone
  // (it may name a class, possibly one declared elsewhere) to avoid false
  // positives.
  auto definitely_not_a_class = [&](const DataType* bound) -> bool {
    return bound->kind != DataTypeKind::kNamed;
  };

  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    if (item->typedef_type.kind != DataTypeKind::kNamed) continue;
    auto scope = item->typedef_type.scope_name;
    if (scope.empty()) continue;
    auto it = type_param_bound.find(scope);
    if (it == type_param_bound.end()) continue;
    if (definitely_not_a_class(it->second)) {
      diag_.Error(item->loc,
                  std::format("type parameter '{}' used as a class scope "
                              "resolution prefix does not resolve to a class",
                              scope));
    }
  }
}

void Elaborator::ValidateForwardClassTypedefs() {
  for (const auto* item : unit_->cu_items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    if (item->typedef_type.kind != DataTypeKind::kImplicit) continue;
    bool resolved = false;
    for (const auto* cls : unit_->classes) {
      if (cls->name == item->name) {
        resolved = true;
        break;
      }
    }
    if (!resolved) {
      for (const auto* other : unit_->cu_items) {
        if (other == item) continue;
        if (other->kind == ModuleItemKind::kTypedef &&
            other->name == item->name &&
            other->typedef_type.kind != DataTypeKind::kImplicit) {
          resolved = true;
          break;
        }
      }
    }
    if (!resolved) {
      diag_.Error(item->loc,
                  std::format("forward typedef '{}' is never resolved by a "
                              "definition in the same scope",
                              item->name));
    }
  }
}

// 18.4: a real variable shall not be declared randc. The randc cyclic
// semantics are defined only over an integral declared range, so a real
// property may carry rand but never randc.
static bool IsRealDataType(DataTypeKind kind) {
  return kind == DataTypeKind::kReal || kind == DataTypeKind::kShortreal ||
         kind == DataTypeKind::kRealtime;
}

void Elaborator::ValidateOneClassRandomVariables(const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kProperty) continue;
    const DataType& dt = m->data_type;

    // A real variable shall not be declared randc.
    if (m->is_randc && IsRealDataType(dt.kind)) {
      diag_.Error(m->loc,
                  std::format("real variable '{}' shall not be declared randc",
                              m->name));
    }

    // An object handle may be declared rand but never randc: randomization
    // solves the referenced object's variables and never reassigns the handle
    // itself, so there is no cyclic value sequence for randc to permute.
    if (m->is_randc && dt.kind == DataTypeKind::kNamed &&
        FindClassDecl(dt.type_name, unit_) != nullptr) {
      diag_.Error(m->loc,
                  std::format("object handle '{}' shall not be declared randc",
                              m->name));
    }

    if (m->is_rand || m->is_randc) {
      // Resolve the declared type through any typedef chain so that a union
      // hidden behind a named type is still examined.
      const DataType* resolved = &dt;
      for (int hops = 0; hops < 8 && resolved->kind == DataTypeKind::kNamed;
           ++hops) {
        auto it = typedefs_.find(resolved->type_name);
        if (it == typedefs_.end()) break;
        resolved = &it->second;
      }
      // Only a packed untagged union may be randomized: it is treated as an
      // integral value. An unpacked union has no single integral image, and a
      // packed tagged union carries a tag that randomization cannot honor.
      if (resolved->kind == DataTypeKind::kUnion) {
        if (!resolved->is_packed) {
          diag_.Error(m->loc,
                      std::format("unpacked union '{}' shall not be declared "
                                  "rand or randc",
                                  m->name));
        } else if (resolved->is_tagged) {
          diag_.Error(m->loc,
                      std::format("packed tagged union '{}' shall not be "
                                  "declared rand or randc",
                                  m->name));
        }
      }
    }
  }
}

void Elaborator::ValidateRandomVariableTypes() {
  for (const auto* cls : unit_->classes) ValidateOneClassRandomVariables(cls);
}

// 18.5: constraint block names shall be unique within a class.
void Elaborator::ValidateOneClassConstraintNames(const ClassDecl* cls) {
  std::unordered_set<std::string_view> seen;
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    if (m->name.empty()) continue;
    if (!seen.insert(m->name).second) {
      diag_.Error(m->loc,
                  std::format("constraint block name '{}' is not unique "
                              "within class '{}'",
                              m->name, cls->name));
    }
  }
}

void Elaborator::ValidateConstraintBlockNames() {
  for (const auto* cls : unit_->classes) ValidateOneClassConstraintNames(cls);
}

// 18.5.7.1: the dimension count of a class property whose dimensions are fully
// visible on its declaration — its packed dimensions plus its unpacked
// dimensions.
static int ConstraintArrayDimCount(const ClassMember* m) {
  int packed = (m->data_type.packed_dim_left != nullptr ? 1 : 0) +
               static_cast<int>(m->data_type.extra_packed_dims.size());
  int unpacked = static_cast<int>(m->unpacked_dims.size());
  return packed + unpacked;
}

// 18.5.7.1: a simple integral/vector type whose dimensionality is determined
// entirely by its own declaration. The loop-variable-count check is confined to
// these so that a typedef'd or aggregate element type, which may contribute
// hidden packed dimensions, is conservatively left alone.
static bool IsSimpleIntegralVectorKind(DataTypeKind k) {
  switch (k) {
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kBit:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
      return true;
    default:
      return false;
  }
}

// 18.5.7.1: in a foreach iterative constraint the number of loop variables
// shall not exceed the number of dimensions of the iterated array. The array is
// a class property, possibly inherited, so resolve the name through the class
// and its base-class chain; a derived declaration shadows a base one. Only
// simple integral/vector arrays with at least one dimension are checked, which
// excludes scalars (not array variables, hence outside this rule) and complex
// types whose dimensionality is not fully visible.
void Elaborator::ValidateOneClassForeachConstraintDims(const ClassDecl* cls) {
  std::unordered_map<std::string_view, const ClassMember*> properties;
  for (const ClassDecl* c = cls; c;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit_)) {
    for (const auto* m : c->members) {
      if (m->kind != ClassMemberKind::kProperty || m->name.empty()) continue;
      properties.emplace(m->name, m);  // keeps the most-derived binding
    }
  }

  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    for (const auto& fe : m->constraint_foreach_refs) {
      auto it = properties.find(fe.array_name);
      if (it == properties.end()) continue;
      if (!IsSimpleIntegralVectorKind(it->second->data_type.kind)) continue;
      int dims = ConstraintArrayDimCount(it->second);
      if (dims < 1) continue;  // not an array variable: not this rule's concern
      if (fe.loop_var_count > dims) {
        diag_.Error(
            fe.loc,
            std::format("foreach iterative constraint lists {} loop "
                        "variable(s) but array '{}' has only {} dimension(s)",
                        fe.loop_var_count, fe.array_name, dims));
      }
    }
  }
}

void Elaborator::ValidateForeachConstraintDims() {
  for (const auto* cls : unit_->classes)
    ValidateOneClassForeachConstraintDims(cls);
}

// 18.5.9: a variable named in a solve...before ordering shall be of integral or
// real type. Reject the types that are plainly neither — strings, events,
// chandles, virtual interfaces, void, and class handles. A typedef name is left
// alone (its underlying type is assumed orderable), keeping the check
// conservative so it never flags a legitimate integral or real variable.
bool Elaborator::IsSolveOrderableType(const DataType& dt) const {
  switch (dt.kind) {
    case DataTypeKind::kString:
    case DataTypeKind::kEvent:
    case DataTypeKind::kChandle:
    case DataTypeKind::kVirtualInterface:
    case DataTypeKind::kVoid:
      return false;
    case DataTypeKind::kNamed:
      return FindClassDecl(dt.type_name, unit_) == nullptr;
    default:
      return true;
  }
}

// 18.5.9: the restrictions that apply to solve...before variable ordering:
//   - only random variables are allowed (they shall be rand);
//   - randc variables are not allowed (they are always solved before any other);
//   - the variables shall be integral or real;
//   - there shall be no circular dependency in the ordering.
// As with the foreach dimension check, resolve each named variable against the
// class and its base chain (a derived declaration shadows a base one), and apply
// the rand/integral restrictions only to simple local identifiers that resolve
// to a property — a hierarchical reference or an array.size() method (expressly
// allowed as an ordering variable) is left alone.
void Elaborator::ValidateOneClassSolveBeforeConstraints(const ClassDecl* cls) {
  std::unordered_map<std::string_view, const ClassMember*> properties;
  for (const ClassDecl* c = cls; c;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit_)) {
    for (const auto* m : c->members) {
      if (m->kind != ClassMemberKind::kProperty || m->name.empty()) continue;
      properties.emplace(m->name, m);  // keeps the most-derived binding
    }
  }

  // Aggregate every ordering edge (a variable solved before another) across the
  // class's constraint blocks so a circular dependency that spans more than one
  // solve statement is still detected.
  std::unordered_map<std::string_view, std::vector<std::string_view>> succ;
  std::unordered_set<std::string_view> nodes;
  bool have_loc = false;
  SourceLoc report_loc;

  auto check_entry = [&](const ConstraintSolveBeforeEntry& e,
                         const SourceLoc& loc) {
    if (!e.is_simple) return;  // hierarchical ref or array.size(): allowed
    auto it = properties.find(e.name);
    if (it == properties.end()) return;  // not a local property: leave alone
    const ClassMember* prop = it->second;
    if (prop->is_randc) {
      diag_.Error(loc, std::format("randc variable '{}' is not allowed in a "
                                   "solve...before ordering constraint",
                                   e.name));
      return;
    }
    if (!prop->is_rand) {
      diag_.Error(loc, std::format("'{}' is not a random variable and cannot "
                                   "appear in a solve...before ordering "
                                   "constraint",
                                   e.name));
      return;
    }
    if (!IsSolveOrderableType(prop->data_type)) {
      diag_.Error(loc,
                  std::format("solve...before ordering variable '{}' shall be "
                              "of integral or real type",
                              e.name));
    }
  };

  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    for (const auto& ref : m->constraint_solve_before_refs) {
      if (!have_loc) {
        report_loc = ref.loc;
        have_loc = true;
      }
      for (const auto& e : ref.before) check_entry(e, ref.loc);
      for (const auto& e : ref.after) check_entry(e, ref.loc);
      // Build the ordering graph only over plain variable names. A qualified or
      // array-method primary (e.g. two different arrays' size() both reduce to
      // the leaf 'size') could otherwise collide into a spurious cycle.
      for (const auto& b : ref.before) {
        if (!b.is_simple) continue;
        for (const auto& a : ref.after) {
          if (!a.is_simple) continue;
          succ[b.name].push_back(a.name);
          nodes.insert(b.name);
          nodes.insert(a.name);
        }
      }
    }
  }

  // Depth-first cycle detection over the ordering graph. A gray (on-stack)
  // successor closes a cycle, such as 'solve a before b' combined with 'solve b
  // before a' (or a degenerate 'solve a before a').
  std::unordered_map<std::string_view, int> color;  // 0 white, 1 gray, 2 black
  bool has_cycle = false;
  std::function<void(std::string_view)> dfs = [&](std::string_view v) {
    color[v] = 1;
    for (std::string_view w : succ[v]) {
      if (color[w] == 1) {
        has_cycle = true;
        return;
      }
      if (color[w] == 0) {
        dfs(w);
        if (has_cycle) return;
      }
    }
    color[v] = 2;
  };
  for (std::string_view v : nodes) {
    if (color[v] == 0) {
      dfs(v);
      if (has_cycle) break;
    }
  }
  if (has_cycle) {
    diag_.Error(report_loc,
                "circular dependency in solve...before variable ordering");
  }
}

void Elaborator::ValidateSolveBeforeConstraints() {
  for (const auto* cls : unit_->classes)
    ValidateOneClassSolveBeforeConstraints(cls);
}

// 18.5.13.1: soft constraints can only be specified on random variables; they
// may not be specified for randc variables. Resolve each bare local variable
// named in a soft constraint expression against the class and its base chain
// (a derived declaration shadows a base one) and reject one that resolves to a
// randc property. As with the solve...before and foreach checks, only simple
// local identifiers the parser recorded are considered; a qualified reference
// or one that does not resolve to a local property is left alone.
void Elaborator::ValidateOneClassSoftConstraintVariables(const ClassDecl* cls) {
  std::unordered_map<std::string_view, const ClassMember*> properties;
  for (const ClassDecl* c = cls; c;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit_)) {
    for (const auto* m : c->members) {
      if (m->kind != ClassMemberKind::kProperty || m->name.empty()) continue;
      properties.emplace(m->name, m);  // keeps the most-derived binding
    }
  }

  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    for (const auto& ref : m->constraint_soft_refs) {
      auto it = properties.find(ref.name);
      if (it == properties.end()) continue;  // not a local property
      if (it->second->is_randc) {
        diag_.Error(ref.loc,
                    std::format("a soft constraint may not be specified on "
                                "randc variable '{}'",
                                ref.name));
      }
    }
  }
}

void Elaborator::ValidateSoftConstraintVariables() {
  for (const auto* cls : unit_->classes)
    ValidateOneClassSoftConstraintVariables(cls);
}

// 18.5.11: locate a function method of the given name visible in 'cls' or any of
// its base classes, returning its ModuleItem (the function declaration) or
// nullptr. The nearest declaration wins, matching ordinary method lookup.
static const ModuleItem* FindClassFunction(const ClassDecl* cls,
                                           std::string_view name,
                                           const CompilationUnit* unit) {
  for (const auto* c = cls; c;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kMethod && m->name == name &&
          m->method && m->method->kind == ModuleItemKind::kFunctionDecl) {
        return m->method;
      }
    }
  }
  return nullptr;
}

// 18.5.11: a function called in a constraint cannot modify the constraints, for
// example by calling rand_mode() or constraint_mode(). Search an expression for
// a member-access call to either built-in method.
static bool ExprCallsModeMethod(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kCall) {
    const Expr* callee = e->lhs;
    if (callee && callee->kind == ExprKind::kMemberAccess && callee->rhs &&
        callee->rhs->kind == ExprKind::kIdentifier &&
        (callee->rhs->text == "rand_mode" ||
         callee->rhs->text == "constraint_mode")) {
      return true;
    }
  }
  if (ExprCallsModeMethod(e->lhs)) return true;
  if (ExprCallsModeMethod(e->rhs)) return true;
  if (ExprCallsModeMethod(e->base)) return true;
  if (ExprCallsModeMethod(e->index)) return true;
  if (ExprCallsModeMethod(e->index_end)) return true;
  if (ExprCallsModeMethod(e->condition)) return true;
  if (ExprCallsModeMethod(e->true_expr)) return true;
  if (ExprCallsModeMethod(e->false_expr)) return true;
  if (ExprCallsModeMethod(e->repeat_count)) return true;
  if (ExprCallsModeMethod(e->with_expr)) return true;
  for (const auto* a : e->args)
    if (ExprCallsModeMethod(a)) return true;
  for (const auto* el : e->elements)
    if (ExprCallsModeMethod(el)) return true;
  return false;
}

// 18.5.11: recursively search a statement (and its substatements and
// subexpressions) for a rand_mode()/constraint_mode() call.
static bool StmtCallsModeMethod(const Stmt* s) {
  if (!s) return false;
  if (ExprCallsModeMethod(s->condition)) return true;
  if (ExprCallsModeMethod(s->lhs)) return true;
  if (ExprCallsModeMethod(s->rhs)) return true;
  if (ExprCallsModeMethod(s->for_cond)) return true;
  if (ExprCallsModeMethod(s->expr)) return true;
  if (ExprCallsModeMethod(s->var_init)) return true;
  for (const auto& ci : s->case_items) {
    for (const auto* p : ci.patterns)
      if (ExprCallsModeMethod(p)) return true;
    if (StmtCallsModeMethod(ci.body)) return true;
  }
  for (const auto& [w, body] : s->randcase_items) {
    if (ExprCallsModeMethod(w)) return true;
    if (StmtCallsModeMethod(body)) return true;
  }
  for (const auto* sub : s->stmts)
    if (StmtCallsModeMethod(sub)) return true;
  for (const auto* sub : s->fork_stmts)
    if (StmtCallsModeMethod(sub)) return true;
  if (StmtCallsModeMethod(s->then_branch)) return true;
  if (StmtCallsModeMethod(s->else_branch)) return true;
  if (StmtCallsModeMethod(s->body)) return true;
  if (StmtCallsModeMethod(s->for_body)) return true;
  for (const auto* fi : s->for_inits)
    if (StmtCallsModeMethod(fi)) return true;
  for (const auto* fs : s->for_steps)
    if (StmtCallsModeMethod(fs)) return true;
  return false;
}

// 18.5.11: enforce the restrictions on a function used in a constraint:
//   - It shall not have output, inout, or (non-const) ref arguments — only
//     input and const ref are permitted, so the call cannot write back into the
//     solver's variables.
//   - It cannot modify the constraints, e.g. by calling rand_mode() or
//     constraint_mode().
// The parser records every unqualified call in a constraint body; here each
// callee that resolves to a method of the enclosing class hierarchy is checked.
// A name that does not resolve to a class function (a free function or an array
// built-in such as size()) is left to other passes.
void Elaborator::ValidateOneClassConstraintFunctionArgs(const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    for (const auto& ref : m->constraint_function_call_refs) {
      const ModuleItem* fn = FindClassFunction(cls, ref.callee, unit_);
      if (!fn) continue;
      for (const auto& arg : fn->func_args) {
        bool bad = arg.direction == Direction::kOutput ||
                   arg.direction == Direction::kInout ||
                   (arg.direction == Direction::kRef && !arg.is_const);
        if (bad) {
          diag_.Error(
              ref.loc,
              std::format("function '{}' used in a constraint shall not have "
                          "output, inout, or non-const ref arguments",
                          ref.callee));
          break;
        }
      }
      for (const auto* s : fn->func_body_stmts) {
        if (StmtCallsModeMethod(s)) {
          diag_.Error(
              ref.loc,
              std::format("function '{}' used in a constraint cannot modify the "
                          "constraints by calling rand_mode or constraint_mode",
                          ref.callee));
          break;
        }
      }
    }
  }
}

void Elaborator::ValidateConstraintFunctionArgs() {
  for (const auto* cls : unit_->classes)
    ValidateOneClassConstraintFunctionArgs(cls);
}

// 18.8: rand_mode() is built-in and cannot be overridden. A user class
// therefore shall not declare a method named rand_mode; doing so is reported
// as an error rather than silently shadowing the built-in method.
void Elaborator::ValidateOneClassBuiltinMethods(const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod) continue;
    if (m->name == "rand_mode") {
      diag_.Error(m->loc,
                  "'rand_mode' is a built-in method and cannot be overridden");
    }
    // 18.9: constraint_mode() is likewise a built-in method that a class may
    // not redefine.
    if (m->name == "constraint_mode") {
      diag_.Error(
          m->loc,
          "'constraint_mode' is a built-in method and cannot be overridden");
    }
    // 18.6.3: randomize() is a built-in method and cannot be overridden, so a
    // user class shall not declare a method named randomize. (pre_randomize and
    // post_randomize are different: 18.6.2 permits overriding those, subject to
    // the prototype check below.)
    if (m->name == "randomize") {
      diag_.Error(m->loc,
                  "'randomize' is a built-in method and cannot be overridden");
    }
    // 18.6.2: pre_randomize() and post_randomize() are built-in methods with a
    // fixed prototype, 'function void <name>();'. Unlike rand_mode and
    // constraint_mode a user may override them, but an override shall match
    // that prototype: a void-returning function taking no arguments. A task
    // form, a non-void return type, or any formal argument does not conform.
    if (m->name == "pre_randomize" || m->name == "post_randomize") {
      const ModuleItem* fn = m->method;
      if (fn) {
        if (fn->kind != ModuleItemKind::kFunctionDecl) {
          diag_.Error(m->loc,
                      std::format("'{}' shall be a void function taking no "
                                  "arguments, not a task",
                                  m->name));
        } else {
          if (fn->return_type.kind != DataTypeKind::kVoid) {
            diag_.Error(
                m->loc,
                std::format("'{}' shall have a void return type", m->name));
          }
          if (!fn->func_args.empty()) {
            diag_.Error(m->loc,
                        std::format("'{}' shall take no arguments", m->name));
          }
        }
      }
    }
  }
}

void Elaborator::ValidateBuiltinRandomizationMethods() {
  for (const auto* cls : unit_->classes) ValidateOneClassBuiltinMethods(cls);
}

// True when location 'a' lies strictly before location 'b' within one file.
// Locations in different files are treated as unordered (returns false).
static bool LocStrictlyBefore(const SourceLoc& a, const SourceLoc& b) {
  if (a.file_id != b.file_id) return false;
  if (a.line != b.line) return a.line < b.line;
  return a.column < b.column;
}

// 18.5.1: an external constraint block completes a constraint prototype.
//   - The explicit prototype form ('extern constraint name;') shall have a
//     corresponding external constraint block.
//   - An implicit prototype ('constraint name;') with no external block is
//     treated as an empty constraint (no effect on randomization); this is
//     legal.
//   - No prototype may be completed by more than one external block.
void Elaborator::ValidateOneClassExternalConstraints(const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    if (!m->is_constraint_prototype) continue;
    // Pure constraints are obligations governed by 18.5.2, not completed by an
    // external block, so they are outside the scope of this check.
    if (m->is_pure_virtual) continue;

    int matches = 0;
    for (const auto& ext : unit_->external_constraints) {
      if (ext.class_name == cls->name && ext.constraint_name == m->name) {
        ++matches;
      }
    }

    if (matches == 0) {
      if (m->is_constraint_extern) {
        diag_.Error(m->loc,
                    std::format("explicit constraint prototype '{}' in class "
                                "'{}' has no external constraint block",
                                m->name, cls->name));
      }
      // Implicit prototype with no external block: empty constraint, legal.
    } else if (matches > 1) {
      diag_.Error(m->loc,
                  std::format("constraint prototype '{}' in class '{}' is "
                              "completed by more than one external constraint "
                              "block",
                              m->name, cls->name));
    }
  }
}

// 18.5.2: walks the superclass chain looking for a constraint of the given
// name. Returns the nearest such constraint member, or nullptr when no base
// class declares one. A derived constraint of the same name replaces it.
static const ClassMember* FindBaseConstraint(const ClassDecl* cls,
                                             std::string_view name,
                                             const CompilationUnit* unit) {
  if (cls->base_class.empty()) return nullptr;
  for (const auto* c = FindClassDecl(cls->base_class, unit); c;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kConstraint && m->name == name) {
        return m;
      }
    }
  }
  return nullptr;
}

// 18.5.2: like FindBaseConstraint but only reports a same-named base
// constraint that was declared with the 'final' specifier, which a subclass
// is forbidden from replacing.
static const ClassMember* FindBaseFinalConstraint(const ClassDecl* cls,
                                                  std::string_view name,
                                                  const CompilationUnit* unit) {
  if (cls->base_class.empty()) return nullptr;
  for (const auto* c = FindClassDecl(cls->base_class, unit); c;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kConstraint && m->name == name &&
          m->is_constraint_final) {
        return m;
      }
    }
  }
  return nullptr;
}

// 18.5.2: enforces the dynamic override specifiers on a single constraint.
//   - ':initial' declares the constraint is not an override, so a same-named
//     base constraint is an error.
//   - ':extends' declares the constraint is an override, so the absence of a
//     same-named base constraint is an error.
//   - ':initial' and ':extends' are mutually exclusive.
//   - Replacing a base constraint declared ':final' is an error.
void Elaborator::ValidateOneConstraintOverride(const ClassDecl* cls,
                                               const ClassMember* m) {
  if (m->is_constraint_initial && m->is_constraint_extends) {
    diag_.Error(m->loc,
                std::format("constraint '{}' shall not specify both ':initial' "
                            "and ':extends'",
                            m->name));
  }

  // 18.5.10: it is illegal to use the dynamic override specifiers ':initial',
  // ':extends', or ':final' on a constraint that is qualified 'static'.
  if (m->is_static &&
      (m->is_constraint_initial || m->is_constraint_extends ||
       m->is_constraint_final)) {
    diag_.Error(m->loc,
                std::format("static constraint '{}' shall not carry a dynamic "
                            "override specifier",
                            m->name));
  }

  const auto* base = FindBaseConstraint(cls, m->name, unit_);

  // 18.5.10: a pure constraint may be qualified 'static', and an overriding
  // constraint shall match that qualification — static if the pure constraint
  // is static, non-static if it is not.
  if (base != nullptr && base->is_pure_virtual && !m->is_pure_virtual &&
      m->is_static != base->is_static) {
    diag_.Error(m->loc,
                std::format("constraint '{}' overriding a pure constraint shall "
                            "match its 'static' qualification",
                            m->name));
  }

  if (m->is_constraint_initial && base) {
    diag_.Error(m->loc,
                std::format("constraint '{}' declared ':initial' overrides a "
                            "constraint of the same name in a base class",
                            m->name));
  }
  if (m->is_constraint_extends && !base) {
    diag_.Error(m->loc,
                std::format("constraint '{}' declared ':extends' does not "
                            "override a constraint in a base class",
                            m->name));
  }

  if (base != nullptr && FindBaseFinalConstraint(cls, m->name, unit_)) {
    diag_.Error(m->loc,
                std::format("constraint '{}' replaces a base class constraint "
                            "declared ':final'",
                            m->name));
  }
}

// 18.5.2: gathers the names of pure constraints inherited by 'cls' that no
// class on the path down to 'cls' has overridden with a non-pure constraint.
static void CollectInheritedPureConstraints(
    const ClassDecl* cls, const CompilationUnit* unit,
    std::vector<std::string_view>& pure_names) {
  if (!cls) return;
  if (!cls->base_class.empty()) {
    CollectInheritedPureConstraints(FindClassDecl(cls->base_class, unit), unit,
                                    pure_names);
  }
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    if (m->is_pure_virtual) {
      pure_names.push_back(m->name);
    } else {
      // A non-pure constraint of the same name overrides the obligation.
      std::erase(pure_names, m->name);
    }
  }
}

// 18.5.2: a non-abstract class shall provide an implementation for every pure
// constraint it inherits, and a pure constraint shall not be declared in a
// non-abstract class.
void Elaborator::ValidateNonAbstractPureConstraints(const ClassDecl* cls) {
  if (cls->is_virtual) return;

  std::vector<std::string_view> unimpl;
  if (!cls->base_class.empty()) {
    CollectInheritedPureConstraints(FindClassDecl(cls->base_class, unit_),
                                    unit_, unimpl);
  }
  // Constraints declared in this class override any inherited obligation of
  // the same name; only a same-named non-pure constraint discharges it.
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kConstraint && !m->is_pure_virtual) {
      std::erase(unimpl, m->name);
    }
  }
  for (auto name : unimpl) {
    diag_.Error(cls->range.start,
                std::format("non-abstract class '{}' does not implement "
                            "inherited pure constraint '{}'",
                            cls->name, name));
  }
}

// 18.5.2: a constraint completed by a prototype plus an external constraint
// block shall carry the same dynamic override specifiers on both the prototype
// and the external block, or on neither.
void Elaborator::ValidateConstraintSpecifierParity(const ClassDecl* cls,
                                                   const ClassMember* m) {
  for (const auto& ext : unit_->external_constraints) {
    if (ext.class_name != cls->name || ext.constraint_name != m->name) continue;
    if (m->is_constraint_initial != ext.is_initial ||
        m->is_constraint_extends != ext.is_extends ||
        m->is_constraint_final != ext.is_final) {
      diag_.Error(
          ext.loc,
          std::format("external constraint block '{}::{}' and its prototype "
                      "disagree on dynamic override specifiers",
                      cls->name, m->name));
    }
    // 18.5.10: the 'static' keyword shall be applied to both the constraint
    // prototype and the external constraint block, or to neither.
    if (m->is_static != ext.is_static) {
      diag_.Error(
          ext.loc,
          std::format("external constraint block '{}::{}' and its prototype "
                      "disagree on the 'static' qualifier",
                      cls->name, m->name));
    }
  }
}

void Elaborator::ValidateConstraintInheritance() {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kConstraint) continue;
      // 18.5.2: a pure constraint is an obligation and may only appear in an
      // abstract (virtual) class.
      if (m->is_pure_virtual && !cls->is_virtual) {
        diag_.Error(m->loc,
                    std::format("pure constraint '{}' shall not be declared in "
                                "non-abstract class '{}'",
                                m->name, cls->name));
      }
      // 18.5.2: a class that declares a pure constraint shall not also complete
      // a constraint of the same name with an external constraint block, nor
      // declare a same-name constraint block or constraint prototype in the
      // same class body.
      if (m->is_pure_virtual) {
        for (const auto& ext : unit_->external_constraints) {
          if (ext.class_name == cls->name && ext.constraint_name == m->name) {
            diag_.Error(
                ext.loc,
                std::format("external constraint block '{}::{}' conflicts with "
                            "a pure constraint of the same name",
                            cls->name, m->name));
            break;
          }
        }
        for (const auto* other : cls->members) {
          if (other == m) continue;
          if (other->kind != ClassMemberKind::kConstraint) continue;
          if (other->name != m->name) continue;
          if (other->is_pure_virtual) continue;
          diag_.Error(other->loc,
                      std::format("constraint '{}' in class '{}' conflicts "
                                  "with a pure constraint of the same name",
                                  other->name, cls->name));
        }
      } else if (m->is_constraint_prototype) {
        ValidateConstraintSpecifierParity(cls, m);
      }
      ValidateOneConstraintOverride(cls, m);
    }
    ValidateNonAbstractPureConstraints(cls);
  }
}

void Elaborator::ValidateExternalConstraints() {
  for (const auto* cls : unit_->classes) {
    ValidateOneClassExternalConstraints(cls);
  }

  // 18.5.1: an external constraint block shall appear in the same scope as its
  // class declaration and after that class declaration. The block and the
  // top-level class share a scope here; flag a block that precedes the end of
  // its class declaration.
  for (const auto& ext : unit_->external_constraints) {
    const ClassDecl* target = nullptr;
    for (const auto* cls : unit_->classes) {
      if (cls->name == ext.class_name) {
        target = cls;
        break;
      }
    }
    if (target == nullptr) continue;
    if (!LocStrictlyBefore(target->range.end, ext.loc)) {
      diag_.Error(ext.loc,
                  std::format("external constraint block '{}::{}' shall appear "
                              "after the declaration of class '{}'",
                              ext.class_name, ext.constraint_name,
                              ext.class_name));
    }
  }
}

}
