#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "elaborator/unit_param_values.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

struct BitsDynamicNames {
  const std::unordered_set<std::string_view>& dyn_types;
  const std::unordered_set<std::string_view>& dyn_funcs;
  const std::unordered_set<std::string_view>& iface_vars;
};

bool IsBitsCall(const Expr* e) {
  return e && e->kind == ExprKind::kSystemCall && e->callee == "$bits" &&
         e->args.size() == 1 && e->args[0];
}

void CheckBitsCallIdentArg(const Expr* call, const Expr* a,
                           const BitsDynamicNames& names, DiagEngine& diag) {
  if (names.dyn_types.count(a->text) != 0) {
    diag.Error(call->range.start,
               std::format("'$bits' cannot be applied directly to "
                           "dynamically sized type '{}'",
                           a->text),
               Subclause("20.6.2"));
  }
  if (names.iface_vars.count(a->text) != 0) {
    diag.Error(call->range.start,
               std::format("'$bits' shall not be applied to interface "
                           "class object '{}'",
                           a->text),
               Subclause("20.6.2"));
  }
}

void CheckBitsCallFuncArg(const Expr* call, const Expr* a,
                          const BitsDynamicNames& names, DiagEngine& diag) {
  std::string_view name = a->callee;
  if (name.empty() && a->lhs && a->lhs->kind == ExprKind::kIdentifier)
    name = a->lhs->text;
  if (!name.empty() && names.dyn_funcs.count(name) != 0) {
    diag.Error(call->range.start,
               std::format("'$bits' shall not enclose function '{}' "
                           "whose return type is dynamically sized",
                           name),
               Subclause("20.6.2"));
  }
}

void CheckBitsCallArg(const Expr* call, const Expr* a,
                      const BitsDynamicNames& names, DiagEngine& diag) {
  if (a->kind == ExprKind::kIdentifier) {
    CheckBitsCallIdentArg(call, a, names, diag);
  } else if (a->kind == ExprKind::kCall) {
    CheckBitsCallFuncArg(call, a, names, diag);
  }
}

void CheckBitsCallExpr(const Expr* e, const BitsDynamicNames& names,
                       DiagEngine& diag) {
  if (!e) return;
  if (IsBitsCall(e)) {
    CheckBitsCallArg(e, e->args[0], names, diag);
  }
  CheckBitsCallExpr(e->lhs, names, diag);
  CheckBitsCallExpr(e->rhs, names, diag);
  CheckBitsCallExpr(e->condition, names, diag);
  CheckBitsCallExpr(e->true_expr, names, diag);
  CheckBitsCallExpr(e->false_expr, names, diag);
  CheckBitsCallExpr(e->base, names, diag);
  CheckBitsCallExpr(e->index, names, diag);
  CheckBitsCallExpr(e->index_end, names, diag);
  CheckBitsCallExpr(e->repeat_count, names, diag);
  CheckBitsCallExpr(e->with_expr, names, diag);
  CheckBitsCallExpr(e->stream_range, names, diag);
  for (auto* a : e->args) CheckBitsCallExpr(a, names, diag);
  for (auto* el : e->elements) CheckBitsCallExpr(el, names, diag);
}

void CheckBitsCallStmt(const Stmt* s, const BitsDynamicNames& names,
                       DiagEngine& diag) {
  if (!s) return;
  CheckBitsCallExpr(s->condition, names, diag);
  CheckBitsCallExpr(s->lhs, names, diag);
  CheckBitsCallExpr(s->rhs, names, diag);
  CheckBitsCallExpr(s->expr, names, diag);
  CheckBitsCallExpr(s->delay, names, diag);
  CheckBitsCallExpr(s->var_init, names, diag);
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckBitsCallStmt(sub, names, diag); });
}

std::unordered_set<std::string_view> CollectDynamicTypes(
    const ModuleDecl* decl) {
  std::unordered_set<std::string_view> dyn_types;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTypedef &&
        TypedefHasDynamicDim(item->unpacked_dims)) {
      dyn_types.insert(item->name);
    }
  }
  return dyn_types;
}

std::unordered_set<std::string_view> CollectDynamicFuncs(
    const ModuleDecl* decl,
    const std::unordered_set<std::string_view>& dyn_types) {
  std::unordered_set<std::string_view> dyn_funcs;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kFunctionDecl) continue;
    if (item->return_type.kind == DataTypeKind::kNamed &&
        dyn_types.count(item->return_type.type_name) != 0) {
      dyn_funcs.insert(item->name);
    }
  }
  return dyn_funcs;
}

}  // namespace

void Elaborator::ValidateBitsCallRestrictions(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> dyn_types = CollectDynamicTypes(decl);
  std::unordered_set<std::string_view> dyn_funcs =
      CollectDynamicFuncs(decl, dyn_types);
  std::unordered_set<std::string_view> iface_vars;
  for (const auto& [vname, cls_name] : class_var_types_) {
    const auto* cls = FindClassDecl(cls_name, unit_);
    if (cls && cls->is_interface) iface_vars.insert(vname);
  }
  if (dyn_types.empty() && dyn_funcs.empty() && iface_vars.empty()) return;

  const BitsDynamicNames kNames{dyn_types, dyn_funcs, iface_vars};
  for (const auto* item : decl->items) {
    if (item->body) CheckBitsCallStmt(item->body, kNames, diag_);
    for (auto* s : item->func_body_stmts) CheckBitsCallStmt(s, kNames, diag_);
    CheckBitsCallExpr(item->init_expr, kNames, diag_);
  }
}

static bool IsConstantBitSelect(const Expr* e, const ScopeMap& scope) {
  if (e->is_part_select_plus || e->is_part_select_minus) {
    return ConstEvalInt(e->index, scope).has_value() &&
           ConstEvalInt(e->index_end, scope).has_value();
  }
  if (e->index && e->index_end) return true;
  if (e->index && !e->index_end) {
    return ConstEvalInt(e->index, scope).has_value();
  }
  return true;
}

bool SelectPathIsConstant(const Expr* e, const ScopeMap& scope) {
  while (e->kind == ExprKind::kSelect || e->kind == ExprKind::kMemberAccess) {
    if (e->kind == ExprKind::kMemberAccess) {
      e = e->lhs;
      continue;
    }
    if (!IsConstantBitSelect(e, scope)) return false;
    e = e->base;
  }
  return true;
}

namespace {

bool ExprNamesSignal(const Expr* e,
                     const std::unordered_set<std::string_view>& signals);

bool ScalarChildNamesSignal(
    const Expr* e, const std::unordered_set<std::string_view>& signals) {
  for (const Expr* child : {e->lhs, e->rhs, e->condition, e->true_expr,
                            e->false_expr, e->base, e->index, e->index_end,
                            e->with_expr, e->stream_range, e->repeat_count}) {
    if (ExprNamesSignal(child, signals)) return true;
  }
  return false;
}

bool ExprNamesSignal(const Expr* e,
                     const std::unordered_set<std::string_view>& signals) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier) return signals.count(e->text) > 0;
  if (e->kind == ExprKind::kSystemCall && IsConstantWhateverItsArguments(e))
    return false;
  if (ScalarChildNamesSignal(e, signals)) return true;
  for (const auto* a : e->args)
    if (ExprNamesSignal(a, signals)) return true;
  for (const auto* el : e->elements)
    if (ExprNamesSignal(el, signals)) return true;
  return false;
}

using PackedDims = std::vector<std::pair<int64_t, int64_t>>;

struct DeclaredShape {
  size_t unpacked_count = 0;
  PackedDims packed;
};

using ShapeMap = std::unordered_map<std::string_view, DeclaredShape>;

struct PartSelectBoundsCtx {
  const std::unordered_set<std::string_view>& signals;
  const ShapeMap& shapes;
  const ScopeMap& scope;
  DiagEngine& diag;
};

struct AddressedBase {
  std::string_view name;
  size_t addresses = 0;
};

AddressedBase FindAddressedBase(const Expr* base) {
  AddressedBase found;
  for (const Expr* cur = base; cur != nullptr; cur = cur->base) {
    if (cur->kind == ExprKind::kIdentifier) {
      found.name = cur->text;
      return found;
    }
    if (cur->kind != ExprKind::kSelect) break;
    if (!cur->index || cur->index_end || cur->is_part_select_plus ||
        cur->is_part_select_minus)
      break;
    ++found.addresses;
  }
  return {};
}

const std::pair<int64_t, int64_t>* GoverningRange(const DeclaredShape& shape,
                                                  size_t addresses) {
  if (addresses < shape.unpacked_count) return nullptr;
  size_t index = addresses - shape.unpacked_count;
  if (index >= shape.packed.size()) return nullptr;
  return &shape.packed[index];
}

void CheckOnePartSelectBounds(const Expr* e,
                              const std::pair<int64_t, int64_t>& range,
                              const PartSelectBoundsCtx& ctx) {
  if (ExprNamesSignal(e->index, ctx.signals) ||
      ExprNamesSignal(e->index_end, ctx.signals)) {
    ctx.diag.Error(e->range.start,
                   "non-indexed part-select bounds shall be constant "
                   "expressions",
                   Subclause("11.5.1"));
    return;
  }
  auto msb = ConstEvalInt(e->index, ctx.scope);
  auto lsb = ConstEvalInt(e->index_end, ctx.scope);
  if (!msb || !lsb) return;
  bool descending = range.first >= range.second;
  bool reversed = descending ? (*msb < *lsb) : (*msb > *lsb);
  if (reversed)
    ctx.diag.Error(e->range.start,
                   "part-select's first index must address a more "
                   "significant bit than its second index",
                   Subclause("11.5.1"));
}

void CheckPartSelectNode(const Expr* e, const PartSelectBoundsCtx& ctx) {
  if (e->kind != ExprKind::kSelect || !e->index || !e->index_end) return;
  if (e->is_part_select_plus || e->is_part_select_minus) return;
  auto base = FindAddressedBase(e->base);
  auto it = ctx.shapes.find(base.name);
  if (it == ctx.shapes.end()) return;
  const auto* range = GoverningRange(it->second, base.addresses);
  if (range == nullptr) return;
  CheckOnePartSelectBounds(e, *range, ctx);
}

void CheckPartSelectBoundsExpr(const Expr* e, const PartSelectBoundsCtx& ctx) {
  if (!e) return;
  CheckPartSelectNode(e, ctx);
  CheckPartSelectBoundsExpr(e->lhs, ctx);
  CheckPartSelectBoundsExpr(e->rhs, ctx);
  CheckPartSelectBoundsExpr(e->condition, ctx);
  CheckPartSelectBoundsExpr(e->true_expr, ctx);
  CheckPartSelectBoundsExpr(e->false_expr, ctx);
  CheckPartSelectBoundsExpr(e->base, ctx);
  CheckPartSelectBoundsExpr(e->index, ctx);
  CheckPartSelectBoundsExpr(e->index_end, ctx);
  CheckPartSelectBoundsExpr(e->with_expr, ctx);
  CheckPartSelectBoundsExpr(e->stream_range, ctx);
  CheckPartSelectBoundsExpr(e->repeat_count, ctx);
  for (const auto* a : e->args) CheckPartSelectBoundsExpr(a, ctx);
  for (const auto* el : e->elements) CheckPartSelectBoundsExpr(el, ctx);
}

void CheckPartSelectBoundsStmt(const Stmt* s, const PartSelectBoundsCtx& ctx) {
  if (!s) return;
  CheckPartSelectBoundsExpr(s->lhs, ctx);
  CheckPartSelectBoundsExpr(s->rhs, ctx);
  CheckPartSelectBoundsExpr(s->expr, ctx);
  CheckPartSelectBoundsExpr(s->condition, ctx);
  CheckPartSelectBoundsExpr(s->for_cond, ctx);
  ForEachChildStmt(
      s, [&ctx](Stmt* const& sub) { CheckPartSelectBoundsStmt(sub, ctx); });
}

bool CollectPackedDims(const DataType& type, const ScopeMap& scope,
                       PackedDims& out) {
  if (!type.packed_dim_left || !type.packed_dim_right) return true;
  auto left = ConstEvalInt(type.packed_dim_left, scope);
  auto right = ConstEvalInt(type.packed_dim_right, scope);
  if (!left || !right) return false;
  out.emplace_back(*left, *right);
  for (const auto& [extra_left, extra_right] : type.extra_packed_dims) {
    auto next_left = ConstEvalInt(extra_left, scope);
    auto next_right = ConstEvalInt(extra_right, scope);
    if (!next_left || !next_right) return false;
    out.emplace_back(*next_left, *next_right);
  }
  return true;
}

void CollectProcedureNames(const ModuleDecl* decl,
                           std::unordered_set<std::string_view>& names) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind))
      CollectProcVariableNames(item->body, names);
    for (const auto* s : item->func_body_stmts)
      CollectProcVariableNames(s, names);
    for (const auto& arg : item->func_args) names.insert(arg.name);
  }
}

}  // namespace

void Elaborator::ValidatePartSelectBounds(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> signals;
  ShapeMap shapes;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kVarDecl &&
        item->kind != ModuleItemKind::kNetDecl)
      continue;
    signals.insert(item->name);
    DeclaredShape shape;
    shape.unpacked_count = item->unpacked_dims.size();
    if (!CollectPackedDims(item->data_type, replicate_multiplier_scope_,
                           shape.packed))
      continue;
    if (shape.packed.empty()) continue;
    shapes[item->name] = std::move(shape);
  }
  if (shapes.empty()) return;

  CollectProcedureNames(decl, signals);
  PartSelectBoundsCtx ctx{signals, shapes, replicate_multiplier_scope_, diag_};
  for (const auto* item : decl->items) {
    CheckPartSelectBoundsExpr(item->assign_lhs, ctx);
    CheckPartSelectBoundsExpr(item->assign_rhs, ctx);
    CheckPartSelectBoundsExpr(item->init_expr, ctx);
    CheckPartSelectBoundsStmt(item->body, ctx);
    for (const auto* s : item->func_body_stmts)
      CheckPartSelectBoundsStmt(s, ctx);
  }
}

namespace {

void ReportSpecparamIn(const Expr* value, SourceLoc loc, std::string_view what,
                       const NameSet& visible, DiagEngine& diag) {
  if (value == nullptr) return;
  for (std::string_view specparam : visible) {
    if (!ExprContainsIdent(value, specparam)) continue;
    diag.Error(loc,
               std::format("{} references specparam '{}'", what, specparam),
               Subclause("6.20.5"));
    return;
  }
}

NameSet WithoutNames(NameSet visible, const NameSet& declared) {
  for (std::string_view name : declared) visible.erase(name);
  return visible;
}

void CollectStmtDeclaredNames(const Stmt* s, NameSet& names) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) names.insert(s->var_name);
  ForEachChildStmt(
      s, [&names](const Stmt* sub) { CollectStmtDeclaredNames(sub, names); });
}

void ReportSpecparamInStmt(const Stmt* s, const NameSet& visible,
                           DiagEngine& diag) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl && s->var_is_param)
    ReportSpecparamIn(s->var_init, s->range.start, "parameter", visible, diag);
  ForEachChildStmt(s, [&visible, &diag](const Stmt* sub) {
    ReportSpecparamInStmt(sub, visible, diag);
  });
}

void ReportSpecparamInProcedure(const ModuleItem* item, const NameSet& visible,
                                DiagEngine& diag) {
  NameSet declared;
  for (const auto& arg : item->func_args) declared.insert(arg.name);
  for (const Stmt* s : item->func_body_stmts)
    CollectStmtDeclaredNames(s, declared);
  CollectStmtDeclaredNames(item->body, declared);
  const NameSet kInner = WithoutNames(visible, declared);
  for (const Stmt* s : item->func_body_stmts)
    ReportSpecparamInStmt(s, kInner, diag);
  ReportSpecparamInStmt(item->body, kInner, diag);
}

void ReportSpecparamInClass(const ClassDecl* cls, const NameSet& visible,
                            DiagEngine& diag) {
  if (cls == nullptr) return;
  NameSet declared;
  for (const auto& [name, value] : cls->params) declared.insert(name);
  for (const ClassMember* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty) declared.insert(m->name);
  }
  const NameSet kInner = WithoutNames(visible, declared);
  for (const auto& [name, value] : cls->params) {
    if (value != nullptr)
      ReportSpecparamIn(value, value->range.start, "parameter", kInner, diag);
  }
  for (const ClassMember* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty && m->is_param) {
      ReportSpecparamIn(m->init_expr, m->loc, "parameter", kInner, diag);
    } else if (m->kind == ClassMemberKind::kMethod && m->method != nullptr) {
      ReportSpecparamInProcedure(m->method, kInner, diag);
    } else if (m->kind == ClassMemberKind::kClassDecl) {
      ReportSpecparamInClass(m->nested_class, kInner, diag);
    }
  }
}

void ReportSpecparamInOverrides(const ModuleItem* item, const NameSet& visible,
                                DiagEngine& diag) {
  for (const auto& [name, value] : item->inst_params)
    ReportSpecparamIn(value, item->loc, "parameter override", visible, diag);
}

void ReportSpecparamInItems(const std::vector<ModuleItem*>& items,
                            const NameSet& visible, DiagEngine& diag);

void ReportSpecparamInGenerateBlock(const std::vector<ModuleItem*>& items,
                                    const NameSet& visible, DiagEngine& diag) {
  NameSet declared;
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kParamDecl ||
        item->kind == ModuleItemKind::kVarDecl ||
        item->kind == ModuleItemKind::kNetDecl)
      declared.insert(item->name);
  }
  ReportSpecparamInItems(items, WithoutNames(visible, declared), diag);
}

void ReportSpecparamInGenerate(const ModuleItem* item, const NameSet& visible,
                               DiagEngine& diag) {
  NameSet body_visible = visible;
  if (item->kind == ModuleItemKind::kGenerateFor && item->gen_init &&
      item->gen_init->lhs)
    body_visible.erase(item->gen_init->lhs->text);
  ReportSpecparamInGenerateBlock(item->gen_body, body_visible, diag);
  if (item->gen_else) ReportSpecparamInGenerate(item->gen_else, visible, diag);
  for (const auto& ci : item->gen_case_items)
    ReportSpecparamInGenerateBlock(ci.body, visible, diag);
}

void ReportSpecparamInItems(const std::vector<ModuleItem*>& items,
                            const NameSet& visible, DiagEngine& diag) {
  for (const ModuleItem* item : items) {
    switch (item->kind) {
      case ModuleItemKind::kParamDecl:
        ReportSpecparamIn(item->init_expr, item->loc, "parameter", visible,
                          diag);
        break;
      case ModuleItemKind::kModuleInst:
        ReportSpecparamInOverrides(item, visible, diag);
        break;
      case ModuleItemKind::kGenerateIf:
      case ModuleItemKind::kGenerateCase:
      case ModuleItemKind::kGenerateFor:
        ReportSpecparamInGenerate(item, visible, diag);
        break;
      case ModuleItemKind::kClassDecl:
        ReportSpecparamInClass(item->class_decl, visible, diag);
        break;
      default:
        ReportSpecparamInProcedure(item, visible, diag);
        break;
    }
  }
}

}  // namespace

void Elaborator::ValidateSpecparamInParams(const ModuleDecl* decl) {
  if (specparam_names_.empty()) return;
  ReportSpecparamInItems(decl->items, specparam_names_, diag_);
}

namespace {

void CheckSpecparamInRange(
    const Expr* range, SourceLoc loc,
    const std::unordered_set<std::string_view>& specparam_names,
    DiagEngine& diag) {
  if (!range) return;
  for (const auto& sp : specparam_names) {
    if (ExprContainsIdent(range, sp)) {
      diag.Error(loc,
                 std::format("specparam '{}' may not appear in a "
                             "declaration range specification",
                             sp),
                 Subclause("6.20.5"));
      break;
    }
  }
}

void CheckDeclRangesForSpecparam(
    const ModuleItem* item,
    const std::unordered_set<std::string_view>& specparam_names,
    DiagEngine& diag) {
  CheckSpecparamInRange(item->data_type.packed_dim_left, item->loc,
                        specparam_names, diag);
  CheckSpecparamInRange(item->data_type.packed_dim_right, item->loc,
                        specparam_names, diag);
  for (const auto& [left, right] : item->data_type.extra_packed_dims) {
    CheckSpecparamInRange(left, item->loc, specparam_names, diag);
    CheckSpecparamInRange(right, item->loc, specparam_names, diag);
  }
  for (const auto* dim : item->unpacked_dims) {
    CheckSpecparamInRange(dim, item->loc, specparam_names, diag);
  }
}

}  // namespace

static void ReportHierRefInDeclRange(const ModuleItem* item, DiagEngine& diag);

void Elaborator::ValidateSpecparamInDeclRange(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kNetDecl &&
        item->kind != ModuleItemKind::kVarDecl)
      continue;
    if (!specparam_names_.empty()) {
      CheckDeclRangesForSpecparam(item, specparam_names_, diag_);
    }
    ReportHierRefInDeclRange(item, diag_);
  }
}

static bool ExprContainsHierRef(const Expr* e, const ScopeMap& constants);

static bool AnyExprContainsHierRef(const std::vector<Expr*>& list,
                                   const ScopeMap& constants) {
  for (auto* sub : list) {
    if (ExprContainsHierRef(sub, constants)) return true;
  }
  return false;
}

static bool ExprContainsHierRef(const Expr* e, const ScopeMap& constants) {
  if (!e) return false;

  if (e->kind == ExprKind::kTypeRef) return false;

  if (e->kind == ExprKind::kCall && e->lhs != nullptr &&
      e->lhs->kind == ExprKind::kMemberAccess) {
    return ExprContainsHierRef(e->lhs->lhs, constants) ||
           AnyExprContainsHierRef(e->args, constants);
  }
  if (e->kind == ExprKind::kMemberAccess && BuiltinMethodMember(e) != nullptr)
    return ExprContainsHierRef(e->lhs, constants);
  if (e->kind == ExprKind::kMemberAccess)
    return !e->is_scope_resolution && !IsConstantExpr(e->lhs, constants);
  for (const Expr* sub :
       {e->lhs, e->rhs, e->condition, e->true_expr, e->false_expr}) {
    if (ExprContainsHierRef(sub, constants)) return true;
  }
  return AnyExprContainsHierRef(e->elements, constants) ||
         AnyExprContainsHierRef(e->args, constants);
}

static void ReportHierRefInDeclRange(const ModuleItem* item, DiagEngine& diag) {
  std::vector<Expr*> ranges{item->data_type.packed_dim_left,
                            item->data_type.packed_dim_right};
  for (const auto& [left, right] : item->data_type.extra_packed_dims) {
    ranges.push_back(left);
    ranges.push_back(right);
  }
  ranges.insert(ranges.end(), item->unpacked_dims.begin(),
                item->unpacked_dims.end());
  if (!AnyExprContainsHierRef(ranges, ScopeMap{})) return;
  diag.Error(item->loc,
             std::format("the range of '{}' contains a hierarchical "
                         "reference, which is no constant expression",
                         item->name),
             Subclause("11.2.1"));
}

namespace {

enum class ValueParamKind : uint8_t { kParameter, kLocalparam, kSpecparam };

struct ValueParamValue {
  ValueParamKind kind;
  std::string_view name;
  const Expr* value;
  SourceLoc loc;
};

void ReportNonConstantValue(const ValueParamValue& param,
                            const ScopeMap& constants, DiagEngine& diag) {
  if (param.value == nullptr) return;
  std::string_view noun =
      param.kind == ValueParamKind::kSpecparam ? "specparam" : "parameter";
  if (ExprContainsHierRef(param.value, constants)) {
    diag.Error(param.loc,
               std::format("{} '{}' value contains a hierarchical reference",
                           noun, param.name),
               Subclause("6.20.2"));
    return;
  }
  if (IsConstantExpr(param.value, constants)) return;
  if (param.kind == ValueParamKind::kLocalparam) {
    diag.Error(param.loc,
               std::format("localparam '{}' initializer is not a constant "
                           "expression",
                           param.name),
               Subclause("6.20.4"));
    return;
  }
  diag.Error(param.loc,
             std::format("{} '{}' value is not a constant expression", noun,
                         param.name),
             Subclause("6.20.2"));
}

ScopeMap WithEveryDeclaredConstant(
    ScopeMap scope, const RtlirModule* mod,
    const std::unordered_set<std::string_view>& specparams) {
  for (const auto& param : mod->params) scope.try_emplace(param.name, 0);
  for (std::string_view specparam : specparams) scope.try_emplace(specparam, 0);
  return scope;
}

void ValidatePortListValueParams(const ModuleDecl* decl,
                                 const ScopeMap& constants, DiagEngine& diag) {
  for (const auto& [pname, pval] : decl->params) {
    if (!pval || decl->type_param_names.count(pname)) continue;
    ValueParamKind kind = decl->localparam_port_names.count(pname)
                              ? ValueParamKind::kLocalparam
                              : ValueParamKind::kParameter;
    ReportNonConstantValue({kind, pname, pval, pval->range.start}, constants,
                           diag);
  }
}

void ValidateSpecifyBlockSpecparams(const ModuleItem* block,
                                    const ScopeMap& constants,
                                    DiagEngine& diag) {
  for (const auto* sp : block->specify_items) {
    if (sp->kind != SpecifyItemKind::kSpecparam) continue;
    for (const Expr* value : {sp->param_value, sp->pathpulse_error}) {
      ReportNonConstantValue(
          {ValueParamKind::kSpecparam, sp->param_name, value, sp->loc},
          constants, diag);
    }
  }
}

void ValidateOneValueParam(const ModuleItem* item, const ScopeMap& constants,
                           DiagEngine& diag, bool parameter_is_local = false) {
  if (item->data_type.kind == DataTypeKind::kVoid &&
      item->typedef_type.kind != DataTypeKind::kImplicit)
    return;
  if (!item->init_expr) {
    diag.Error(
        item->loc,
        std::format("value parameter '{}' has no default value", item->name),
        Subclause("6.20.1"));
    return;
  }
  ValueParamKind kind = item->is_localparam || parameter_is_local
                            ? ValueParamKind::kLocalparam
                            : ValueParamKind::kParameter;
  ReportNonConstantValue({kind, item->name, item->init_expr, item->loc},
                         constants, diag);
}

struct GenerateParamCtx {
  const RtlirModule* mod;
  DiagEngine& diag;
  Arena& arena;
};

void AddInstancePrefixes(const ModuleItem* item, const RtlirModule* mod,
                         GenBlockPrefixes& prefixes) {
  for (const auto& pd : mod->params) {
    if (pd.default_value == item->init_expr)
      prefixes.push_back(pd.gen_block_prefix);
  }
}

void ValidateValueParamsInGenerateBody(const std::vector<ModuleItem*>& items,
                                       ScopeMap scope,
                                       GenBlockPrefixes prefixes,
                                       const GenerateParamCtx& ctx);

void ValidateValueParamsInGenerate(const ModuleItem* item,
                                   const ScopeMap& scope,
                                   const GenBlockPrefixes& prefixes,
                                   const GenerateParamCtx& ctx) {
  ScopeMap body_scope = scope;
  if (item->kind == ModuleItemKind::kGenerateFor && item->gen_init &&
      item->gen_init->lhs)
    body_scope[item->gen_init->lhs->text] = 0;
  ValidateValueParamsInGenerateBody(item->gen_body, body_scope, prefixes, ctx);
  if (item->gen_else)
    ValidateValueParamsInGenerate(item->gen_else, scope, prefixes, ctx);
  for (const auto& ci : item->gen_case_items)
    ValidateValueParamsInGenerateBody(ci.body, scope, prefixes, ctx);
}

void ValidateValueParamsInGenerateBody(const std::vector<ModuleItem*>& items,
                                       ScopeMap scope,
                                       GenBlockPrefixes prefixes,
                                       const GenerateParamCtx& ctx) {
  for (const auto* item : items) {
    BindEnumConstantsOfItem(item, scope, ctx.arena);
    if (item->kind == ModuleItemKind::kParamDecl) {
      {
        RegisteredGenScopeGuard in_block(prefixes);
        ValidateOneValueParam(item, scope, ctx.diag, true);
      }
      scope[item->name] = 0;
      AddInstancePrefixes(item, ctx.mod, prefixes);
      continue;
    }
    if (item->kind == ModuleItemKind::kGenerateIf ||
        item->kind == ModuleItemKind::kGenerateCase ||
        item->kind == ModuleItemKind::kGenerateFor)
      ValidateValueParamsInGenerate(item, scope, prefixes, ctx);
  }
}

void BindImportedUnitParamNames(const ModuleItem* item, ScopeMap& scope) {
  if (item->kind != ModuleItemKind::kImportDecl) return;
  for (std::string_view name : UnitParamNamesImported(item->import_item))
    scope.try_emplace(name, 0);
}

}  // namespace

void Elaborator::ValidateValueParams(const ModuleDecl* decl,
                                     const RtlirModule* mod) {
  const ScopeMap kConstants =
      WithEveryDeclaredConstant(BuildParamScope(mod), mod, specparam_names_);
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kParamDecl) {
      ValidateOneValueParam(item, kConstants, diag_);
    } else if (item->kind == ModuleItemKind::kSpecparam) {
      ReportNonConstantValue(
          {ValueParamKind::kSpecparam, item->name, item->init_expr, item->loc},
          kConstants, diag_);
    } else if (item->kind == ModuleItemKind::kSpecifyBlock) {
      ValidateSpecifyBlockSpecparams(item, kConstants, diag_);
    }
  }
  ValidatePortListValueParams(decl, kConstants, diag_);
}

void ValidateGenerateValueParams(const ModuleItem* item, const RtlirModule* mod,
                                 const ScopeMap& scope, DiagEngine& diag,
                                 Arena& arena) {
  GenerateParamCtx ctx{mod, diag, arena};
  ValidateValueParamsInGenerate(
      item,
      WithEveryDeclaredConstant(scope, mod, DeclaredSpecparamNames(mod->decl)),
      {}, ctx);
}

void Elaborator::ValidatePackageValueParams() {
  for (const auto* pkg : unit_->packages) {
    ScopeMap scope = cu_param_scope_;
    for (const auto* item : pkg->items) {
      BindPackageImportConstants(pkg, item, cu_param_scope_, scope);
      BindImportedUnitParamNames(item, scope);
      BindEnumConstantsOfItem(item, scope, arena_);
      if (item->kind != ModuleItemKind::kParamDecl) continue;
      ValidateOneValueParam(item, scope, diag_, true);
      scope[item->name] = 0;
    }
  }
}

}  // namespace delta
