#include <algorithm>
#include <cmath>
#include <format>
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

// §7.6, §7.9.9: Check array assignment compatibility for a pair of exprs.
void Elaborator::CheckArrayAssignExprs(const Expr* lhs, const Expr* rhs,
                                       SourceLoc loc) {
  if (!lhs || !rhs) return;
  if (lhs->kind != ExprKind::kIdentifier) return;
  if (rhs->kind != ExprKind::kIdentifier) return;
  auto lhs_it = var_array_info_.find(lhs->text);
  auto rhs_it = var_array_info_.find(rhs->text);
  if (lhs_it == var_array_info_.end() || rhs_it == var_array_info_.end())
    return;
  const auto& l = lhs_it->second;
  const auto& r = rhs_it->second;
  // §7.9.9
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
  if (l.elem_type != r.elem_type) {
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

// §7.6, §7.9.9: Validate array assignment compatibility.
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

// §7.9.10: Build VarArrayInfo for a formal parameter from its dimensions.
static Elaborator::VarArrayInfo FormalArrayInfo(
    const FunctionArg& arg,
    const std::unordered_set<std::string_view>& class_names) {
  Elaborator::VarArrayInfo info;
  info.elem_type = arg.data_type.kind;
  if (arg.unpacked_dims.empty()) return info;
  auto* dim = arg.unpacked_dims[0];
  if (!dim) {
    info.is_dynamic = true;
    return info;
  }
  if (dim->kind == ExprKind::kIdentifier) {
    auto t = dim->text;
    if (t == "$") return info;  // queue — not assoc or fixed
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
  // Fixed-size array — set a nonzero size to distinguish from scalar.
  info.unpacked_size = 1;
  return info;
}

// §7.9.10: Check a single call's array argument compatibility.
static void CheckArrayArgTypes(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const std::unordered_set<std::string_view>& class_names,
    DiagEngine& diag) {
  if (!expr || expr->kind != ExprKind::kCall || expr->callee.empty()) return;
  auto it = func_decls.find(expr->callee);
  if (it == func_decls.end()) return;
  const auto* func = it->second;
  size_t positional_count = expr->args.size() - expr->arg_names.size();
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    const auto& formal = func->func_args[i];
    auto formal_info = FormalArrayInfo(formal, class_names);
    // Only check when formal is an array parameter.
    if (formal.unpacked_dims.empty()) continue;
    // Resolve actual argument.
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
    }
  }
}

// §7.9.10: Walk expressions for array argument checks.
static void WalkExprForArrayArgTypes(
    const Expr* expr,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const std::unordered_set<std::string_view>& class_names,
    DiagEngine& diag) {
  if (!expr) return;
  CheckArrayArgTypes(expr, func_decls, var_array_info, class_names, diag);
  WalkExprForArrayArgTypes(expr->lhs, func_decls, var_array_info, class_names,
                           diag);
  WalkExprForArrayArgTypes(expr->rhs, func_decls, var_array_info, class_names,
                           diag);
  WalkExprForArrayArgTypes(expr->condition, func_decls, var_array_info,
                           class_names, diag);
  WalkExprForArrayArgTypes(expr->true_expr, func_decls, var_array_info,
                           class_names, diag);
  WalkExprForArrayArgTypes(expr->false_expr, func_decls, var_array_info,
                           class_names, diag);
  for (auto* a : expr->args)
    WalkExprForArrayArgTypes(a, func_decls, var_array_info, class_names, diag);
  for (auto* e : expr->elements)
    WalkExprForArrayArgTypes(e, func_decls, var_array_info, class_names, diag);
}

// §7.9.10: Walk statements for array argument checks.
static void WalkStmtForArrayArgTypes(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>&
        var_array_info,
    const std::unordered_set<std::string_view>& class_names,
    DiagEngine& diag) {
  if (!s) return;
  WalkExprForArrayArgTypes(s->expr, func_decls, var_array_info, class_names,
                           diag);
  WalkExprForArrayArgTypes(s->lhs, func_decls, var_array_info, class_names,
                           diag);
  WalkExprForArrayArgTypes(s->rhs, func_decls, var_array_info, class_names,
                           diag);
  WalkExprForArrayArgTypes(s->condition, func_decls, var_array_info,
                           class_names, diag);
  for (auto* sub : s->stmts)
    WalkStmtForArrayArgTypes(sub, func_decls, var_array_info, class_names,
                             diag);
  WalkStmtForArrayArgTypes(s->then_branch, func_decls, var_array_info,
                           class_names, diag);
  WalkStmtForArrayArgTypes(s->else_branch, func_decls, var_array_info,
                           class_names, diag);
  WalkStmtForArrayArgTypes(s->body, func_decls, var_array_info, class_names,
                           diag);
  WalkStmtForArrayArgTypes(s->for_init, func_decls, var_array_info,
                           class_names, diag);
  WalkStmtForArrayArgTypes(s->for_body, func_decls, var_array_info,
                           class_names, diag);
  WalkStmtForArrayArgTypes(s->for_step, func_decls, var_array_info,
                           class_names, diag);
  WalkExprForArrayArgTypes(s->for_cond, func_decls, var_array_info,
                           class_names, diag);
  for (auto& ci : s->case_items)
    WalkStmtForArrayArgTypes(ci.body, func_decls, var_array_info, class_names,
                             diag);
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
                               class_names_, diag_);
    }
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      for (auto* s : item->func_body_stmts) {
        WalkStmtForArrayArgTypes(s, all_decls, var_array_info_, class_names_,
                                 diag_);
      }
    }
  }
}

// §7.4.6: Detect slice expressions on associative arrays.
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

// §7.9.4–§7.9.7: Traversal methods (first/last/next/prev) shall not be
// called on wildcard-indexed associative arrays.

static bool IsTraversalMethod(std::string_view name) {
  return name == "first" || name == "last" || name == "next" || name == "prev";
}

static void CheckWildcardTraversalExpr(
    const Expr* e,
    const std::unordered_set<std::string_view>& wildcard_names,
    DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kCall && e->base &&
      e->base->kind == ExprKind::kIdentifier &&
      IsTraversalMethod(e->callee) &&
      wildcard_names.count(e->base->text)) {
    diag.Error(e->range.start,
               std::format("'{}' is not allowed on wildcard associative "
                           "array '{}'",
                           e->callee, e->base->text));
  }
  CheckWildcardTraversalExpr(e->lhs, wildcard_names, diag);
  CheckWildcardTraversalExpr(e->rhs, wildcard_names, diag);
  CheckWildcardTraversalExpr(e->base, wildcard_names, diag);
  CheckWildcardTraversalExpr(e->index, wildcard_names, diag);
  CheckWildcardTraversalExpr(e->index_end, wildcard_names, diag);
  CheckWildcardTraversalExpr(e->condition, wildcard_names, diag);
  CheckWildcardTraversalExpr(e->true_expr, wildcard_names, diag);
  CheckWildcardTraversalExpr(e->false_expr, wildcard_names, diag);
  for (const auto* elem : e->elements) {
    CheckWildcardTraversalExpr(elem, wildcard_names, diag);
  }
}

static void WalkStmtsForWildcardTraversal(
    const Stmt* s,
    const std::unordered_set<std::string_view>& wildcard_names,
    DiagEngine& diag) {
  if (!s) return;
  CheckWildcardTraversalExpr(s->lhs, wildcard_names, diag);
  CheckWildcardTraversalExpr(s->rhs, wildcard_names, diag);
  CheckWildcardTraversalExpr(s->expr, wildcard_names, diag);
  CheckWildcardTraversalExpr(s->condition, wildcard_names, diag);
  for (auto* sub : s->stmts)
    WalkStmtsForWildcardTraversal(sub, wildcard_names, diag);
  WalkStmtsForWildcardTraversal(s->then_branch, wildcard_names, diag);
  WalkStmtsForWildcardTraversal(s->else_branch, wildcard_names, diag);
  WalkStmtsForWildcardTraversal(s->body, wildcard_names, diag);
  WalkStmtsForWildcardTraversal(s->for_body, wildcard_names, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForWildcardTraversal(ci.body, wildcard_names, diag);
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
      CheckWildcardTraversalExpr(item->assign_lhs, wildcard_names, diag_);
      CheckWildcardTraversalExpr(item->assign_rhs, wildcard_names, diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForWildcardTraversal(item->body, wildcard_names, diag_);
    }
  }
}

// §7.8.5: real/shortreal shall be an illegal associative array index type.
static bool ContainsRealType(const DataType& dtype, const TypedefMap& tds) {
  if (dtype.kind == DataTypeKind::kNamed) {
    auto it = tds.find(dtype.type_name);
    if (it != tds.end()) return ContainsRealType(it->second, tds);
    return false;
  }
  if (IsRealType(dtype.kind)) return true;
  for (const auto& m : dtype.struct_members) {
    if (IsRealType(m.type_kind)) return true;
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
  // §7.8.5: A type containing real or shortreal is also illegal.
  auto it = typedefs_.find(t);
  if (it != typedefs_.end() && ContainsRealType(it->second, typedefs_)) {
    diag_.Error(item->loc,
                "real or shortreal type shall not be used as an "
                "associative array index type");
  }
}

// --- §8.4: Class handle operator restriction validation ---

static bool IsClassVar(const Expr* e,
                       const std::unordered_set<std::string_view>& class_vars) {
  auto name = ExprIdent(e);
  if (name.empty()) return false;
  return class_vars.count(name) != 0;
}

// §8.4 Table 8-1: Only ==, !=, ===, !== are legal binary ops on class handles.
static bool IsAllowedClassBinaryOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq;
}

// §8.4: Check whether class type `a` is the same as or derived from `b`.
static bool IsClassDerivedFrom(std::string_view a, std::string_view b,
                               const CompilationUnit* unit) {
  if (a == b) return true;
  for (const auto* cls = FindClassDecl(a, unit);
       cls && !cls->base_class.empty();
       cls = FindClassDecl(cls->base_class, unit)) {
    if (cls->base_class == b) return true;
  }
  return false;
}

// §8.4: One of the objects being compared shall be assignment compatible with
// the other; for assignment, the source must be compatible with the target.
static bool AreClassTypesComparable(
    std::string_view type_a, std::string_view type_b,
    const CompilationUnit* unit) {
  return IsClassDerivedFrom(type_a, type_b, unit) ||
         IsClassDerivedFrom(type_b, type_a, unit);
}

static void CheckClassHandleExpr(
    const Expr* e, const std::unordered_set<std::string_view>& class_vars,
    const std::unordered_map<std::string_view, std::string_view>&
        class_var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (!e) return;
  // Binary: only equality operators are allowed.
  if (e->kind == ExprKind::kBinary) {
    bool lhs_class = e->lhs && IsClassVar(e->lhs, class_vars);
    bool rhs_class = e->rhs && IsClassVar(e->rhs, class_vars);
    if ((lhs_class || rhs_class) && !IsAllowedClassBinaryOp(e->op)) {
      diag.Error(e->range.start,
                 "operator is not allowed on class object handles");
    }
    // §8.4: When both operands are class handles, check assignment
    // compatibility.
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
  // Unary: no unary operators are allowed on class handles.
  if (e->kind == ExprKind::kUnary && IsClassVar(e->lhs, class_vars)) {
    diag.Error(e->range.start,
               "operator is not allowed on class object handles");
  }
  // Postfix (++, --): not allowed.
  if (e->kind == ExprKind::kPostfixUnary && IsClassVar(e->lhs, class_vars)) {
    diag.Error(e->range.start,
               "operator is not allowed on class object handles");
  }
  // Bit-select on class handle is illegal.
  if (e->kind == ExprKind::kSelect && e->base &&
      IsClassVar(e->base, class_vars)) {
    diag.Error(e->range.start, "bit-select on class object handle is illegal");
  }
  // Recurse into sub-expressions.
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

void Elaborator::WalkStmtsForClassHandleOps(const Stmt* s) {
  if (!s) return;
  // Check compound assignment to class handle.
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && IsClassVar(s->lhs, class_var_names_)) {
    if (s->rhs && s->rhs->kind == ExprKind::kBinary &&
        IsCompoundAssignOp(s->rhs->op)) {
      diag_.Error(s->range.start,
                  "operator is not allowed on class object handles");
    }
    // §8.4: Assignment of a class object whose class data type is assignment
    // compatible with the target class object.
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
  }
  // Check expressions in assignments, conditions, and expression statements.
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

// §8.10: Check if an expression references 'this' or 'super'.
static bool ExprRefsThisOrSuper(const Expr* e) {
  if (!e) return false;
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

// §8.10: Walk statements looking for 'this'/'super' references.
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

// §8.10: Collect all local variable names declared in a method body.
static void CollectLocalNames(const Stmt* s,
                              std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {
    out.insert(s->var_name);
  }
  if (s->for_init) CollectLocalNames(s->for_init, out);
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

// §8.10: Check if an expression contains an unqualified non-static member ref.
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

// §8.10: Walk statements looking for unqualified non-static member references.
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

// §8.10: Check a single class for static methods referencing this/super
// or unqualified non-static members.
void Elaborator::ValidateOneClassStaticMethods(const ClassDecl* cls) {
  // First pass: check for this/super.
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

  // Collect non-static member names for unqualified access check.
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

  // Second pass: check for unqualified non-static member access.
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

// §8.11: Check a single module item for illegal 'this' usage.
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

// §8.11: 'this' shall only be used within non-static class methods.
void Elaborator::ValidateThisUsage(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    ValidateThisInItem(item);
  }
}

// §8.13: A class declared :final shall not be extended.
void Elaborator::ValidateFinalClassExtension() {
  auto check = [&](const ClassDecl* cls) {
    if (cls->base_class.empty()) return;
    const auto* base = FindClassDecl(cls->base_class, unit_);
    if (base && base->is_final) {
      diag_.Error(cls->range.start, "cannot extend a class declared ':final'");
    }
  };
  for (const auto* cls : unit_->classes) {
    check(cls);
  }
}

// §8.17: Detect if a statement is a super.new() call.
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

// §8.17: Validate chaining constructor rules for a single class.
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
  if (has_super_new && !cls->extends_args.empty()) {
    diag_.Error(ctor->method->loc,
                "constructor shall not contain super.new() when extends "
                "specifier has arguments");
  }
}

// §8.7: Validate class method function bodies (constructors are functions and
// shall be nonblocking; general function body rules from §13.2 apply).
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

// §8.15: Check if an expression references 'super'.
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

// §8.15: Walk statements looking for 'super' references.
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

// §8.15: 'super' shall only be used in a class that extends a base class.
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

// §8.17: Validate chaining constructor rules.
void Elaborator::ValidateChainingConstructors() {
  for (const auto* cls : unit_->classes) {
    ValidateOneClassChainingCtor(cls);
  }
}

// §8.18: Find a class member by name, walking up the hierarchy.
static const ClassMember* FindMemberInClass(const ClassDecl* cls,
                                            std::string_view name,
                                            const CompilationUnit* unit) {
  for (const auto* c = cls; c; /* advance below */) {
    for (const auto* m : c->members) {
      if (m->name == name) return m;
    }
    if (c->base_class.empty()) break;
    c = FindClassDecl(c->base_class, unit);
  }
  return nullptr;
}

// §8.18: Check a single obj.member access for visibility violations.
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
  // §8.5: Accessing a type parameter via a class handle is illegal.
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

// §8.18: Check expressions for local/protected member access from outside
// class.
static void CheckVisibilityExpr(
    const Expr* e,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->lhs && e->rhs) {
    CheckMemberAccessVisibility(e, var_types, unit, diag);
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

// §8.18: Walk statements checking for local/protected access violations.
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

// §8.18: Validate local/protected access from module-level code.
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

// §8.19: Validate constant class property rules.
void Elaborator::ValidateConstClassProperties() {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kProperty || !m->is_const) continue;
      if (!m->init_expr && m->is_static) {
        diag_.Error(m->loc, "instance constant cannot be declared static");
      }
    }
  }
}

// §8.20: Find a virtual method in a base class by name.
static const ClassMember* FindBaseVirtualMethod(const ClassDecl* cls,
                                                std::string_view method_name,
                                                const CompilationUnit* unit) {
  if (cls->base_class.empty()) return nullptr;
  for (const auto* c = FindClassDecl(cls->base_class, unit); c;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kMethod && m->method &&
          m->method->name == method_name && m->is_virtual) {
        return m;
      }
    }
  }
  return nullptr;
}

// §8.20: Validate a single method's override rules within a class.
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
  if (base_virtual && base_virtual->method &&
      base_virtual->method->is_method_final) {
    diag_.Error(method->loc, "cannot override a method declared ':final'");
  }
}

// §8.20: Validate virtual method override rules.
void Elaborator::ValidateVirtualMethodOverrides() {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
      ValidateOneMethodOverride(cls, m);
    }
  }
}

// §8.21: Collect all pure virtual method names from a class and its ancestors.
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

// §8.21: Check that a non-abstract class implements all pure virtual methods.
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

// §8.21: Validate abstract class and pure virtual method rules.
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

static bool HasExternPrototype(const ClassDecl* cls, std::string_view name) {
  return std::any_of(
      cls->members.begin(), cls->members.end(), [name](const auto* m) {
        return m->kind == ClassMemberKind::kMethod && m->method &&
               m->method->name == name && m->method->is_extern;
      });
}

// §8.24: Validate out-of-block method declarations.
void Elaborator::ValidateOutOfBlockDeclarations() {
  std::unordered_set<std::string> linked;
  for (auto* item : unit_->cu_items) {
    if (item->method_class.empty()) continue;
    bool is_func = (item->kind == ModuleItemKind::kFunctionDecl);
    bool is_task = (item->kind == ModuleItemKind::kTaskDecl);
    if (!is_func && !is_task) continue;
    const auto* cls = FindClassDecl(item->method_class, unit_);
    if (!cls) {
      diag_.Error(item->loc,
                  std::format("out-of-block declaration for unknown class '{}'",
                              item->method_class));
      continue;
    }
    bool found_proto = HasExternPrototype(cls, item->name);
    if (!found_proto) {
      diag_.Error(
          item->loc,
          std::format("no matching extern prototype for '{}::{}' in "
                      "class '{}'",
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
  }
}

// §8.26.1: Validate members of an interface class.
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
    }
  }
}

// §8.26.2: Validate inheritance rules for an interface class.
void Elaborator::ValidateInterfaceClassInheritance(const ClassDecl* cls) {
  if (!cls->implements_types.empty()) {
    diag_.Error(cls->range.start,
                std::format("interface class '{}' shall not use "
                            "'implements'",
                            cls->name));
  }
  if (cls->base_class.empty()) return;
  const auto* base = FindClassDecl(cls->base_class, unit_);
  if (base && !base->is_interface) {
    diag_.Error(cls->range.start,
                std::format("interface class '{}' cannot extend "
                            "non-interface class '{}'",
                            cls->name, cls->base_class));
  }
}

// §8.26.2: Validate that a regular class does not extend an interface class.
void Elaborator::ValidateRegularClassInheritance(const ClassDecl* cls) {
  if (cls->base_class.empty()) return;
  const auto* base = FindClassDecl(cls->base_class, unit_);
  if (base && base->is_interface) {
    diag_.Error(cls->range.start,
                std::format("class '{}' cannot extend interface class "
                            "'{}'; use 'implements' instead",
                            cls->name, cls->base_class));
  }
}

// §8.26: Check whether a class hierarchy has a concrete virtual method.
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

static void CheckInterfaceMethods(const ClassDecl* cls, const ClassDecl* iface,
                                  std::string_view iface_name,
                                  const CompilationUnit* unit,
                                  DiagEngine& diag) {
  for (const auto* im : iface->members) {
    if (im->kind != ClassMemberKind::kMethod || !im->is_pure_virtual) continue;
    if (!im->method) continue;
    if (!HasConcreteVirtualMethodInHierarchy(cls, im->method->name, unit)) {
      diag.Error(cls->range.start,
                 std::format("class '{}' does not implement pure virtual "
                             "method '{}' from interface '{}'",
                             cls->name, im->method->name, iface_name));
    }
  }
}

// §8.26: Validate that a non-abstract class implements all interface methods.
void Elaborator::ValidateImplementsInterfaceMethods(const ClassDecl* cls) {
  if (cls->is_virtual || cls->implements_types.empty()) return;
  for (auto iface_name : cls->implements_types) {
    const auto* iface = FindClassDecl(iface_name, unit_);
    if (!iface) continue;
    CheckInterfaceMethods(cls, iface, iface_name, unit_, diag_);
  }
}

// §8.26: Validate interface class rules.
void Elaborator::ValidateInterfaceClassRules() {
  for (const auto* cls : unit_->classes) {
    if (cls->is_interface) {
      ValidateInterfaceClassMembers(cls);
      ValidateInterfaceClassInheritance(cls);
    } else {
      ValidateRegularClassInheritance(cls);
      ValidateImplementsInterfaceMethods(cls);
    }
  }
}

}  // namespace delta
