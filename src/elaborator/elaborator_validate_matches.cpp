#include <format>
#include <functional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/force_lhs.h"
#include "elaborator/net_data_type.h"
#include "elaborator/queue_dim.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

static void CheckLhsPatternNamedKeys(const Expr* lhs, DiagEngine& diag) {
  if (!lhs) return;
  const Expr* pat = lhs;
  if (pat->kind == ExprKind::kCast && pat->lhs) pat = pat->lhs;
  if (pat->kind == ExprKind::kAssignmentPattern && !pat->pattern_keys.empty()) {
    diag.Error(lhs->range.start,
               "LHS assignment pattern shall use positional notation only",
               Subclause("10.9"));
  }
  if (pat->kind == ExprKind::kAssignmentPattern ||
      pat->kind == ExprKind::kConcatenation) {
    for (const Expr* el : pat->elements) CheckLhsPatternNamedKeys(el, diag);
  }
}

static void WalkStmtsForLhsPatternKeys(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckLhsPatternNamedKeys(s->lhs, diag);
  }
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtsForLhsPatternKeys(sub, diag); });
}

void Elaborator::ValidateSubroutineBodyTargets(const ModuleItem* item,
                                               const RtlirModule& mod,
                                               const ScopeMap& scope) {
  if (item->kind != ModuleItemKind::kTaskDecl &&
      item->kind != ModuleItemKind::kFunctionDecl)
    return;
  if (!item->method_class.empty()) return;
  std::unordered_map<std::string_view, SourceLoc> targets;
  CollectProcTargets(item->func_args, item->func_body_stmts, targets);
  ReportProceduralNetTargets(targets);
  const std::unordered_set<std::string_view> kNetNames = NetNamesAt(item->loc);
  ReportProcContAssignNets(item->func_args, item->func_body_stmts, kNetNames,
                           diag_);
  CollectProcContAssignTargets(item->func_args, item->func_body_stmts, targets);
  for (const auto& [name, loc] : targets)
    if (!NamesNet(name, loc)) RecordProcTarget(name, loc);
  const ForceLhsNames kForceNames{kNetNames, nettype_net_names_, mod, typedefs_,
                                  scope};
  for (const Stmt* s : item->func_body_stmts) {
    CheckForceLhs(s, kForceNames, diag_);
    WalkStmtsForLhsPatternKeys(s, diag_);
  }
}

void Elaborator::ValidateItemConstraints(const ModuleItem* item,
                                         const RtlirModule& mod,
                                         const ScopeMap& scope) {
  if (IsProceduralItemKind(item->kind) && item->body) {
    CollectProcTargets({}, {item->body}, proc_assign_targets_);
    std::unordered_map<std::string_view, SourceLoc> assigned;
    CollectProcContAssignTargets({}, {item->body}, assigned);
    std::erase_if(assigned, [this](const auto& target) {
      return NamesNet(target.first, target.second);
    });
    proc_assign_targets_.merge(assigned);
    CollectForceReleaseTargets(item->body, force_release_targets_);
  }
  CheckHighzStrengthPair(item, diag_);
  ValidateItemRules(item, mod, scope);
}

void Elaborator::ValidateItemRules(const ModuleItem* item,
                                   const RtlirModule& mod,
                                   const ScopeMap& scope) {
  bool is_proc = IsProceduralItemKind(item->kind);
  if (is_proc && item->body) {
    CheckInterconnectProcContAssign(item->body, interconnect_names_, diag_);
    CheckInterconnectProceduralRead(item->body, interconnect_names_, diag_);
    CheckProceduralAssignLhs(item->body, diag_);
    const std::unordered_set<std::string_view> kNetNames =
        NetNamesAt(item->loc);
    ReportProcContAssignNets({}, {item->body}, kNetNames, diag_);

    CheckForceLhs(item->body,
                  {kNetNames, nettype_net_names_, mod, typedefs_, scope},
                  diag_);

    CheckBlockQueueBounds(item->body, scope, diag_);

    WalkStmtsForLhsPatternKeys(item->body, diag_);
  }
  ValidateSubroutineBodyTargets(item, mod, scope);
  if (item->kind == ModuleItemKind::kContAssign)
    CheckLhsPatternNamedKeys(item->assign_lhs, diag_);
  ValidateEdgeOnReal(item);
  ValidateChandleContAssign(item);
  ValidateChandleSensitivity(item);
  ValidateVirtualInterfaceContAssign(item);
  ValidateVirtualInterfaceSensitivity(item);
  ValidateClassHandleContAssign(item);

  const SelectOperands kOperands{real_var_names_, real_param_names_,
                                 var_select_shapes_};
  if (item->kind == ModuleItemKind::kContAssign) {
    CheckRealSelect(item->assign_rhs, var_types_, kOperands, diag_);
    CheckRealSelect(item->assign_lhs, var_types_, kOperands, diag_);
    CheckScalarSelect(item->assign_rhs, scalar_var_names_, diag_);
    CheckScalarSelect(item->assign_lhs, scalar_var_names_, diag_);
    CheckIndexedPartSelectWidth(item->assign_rhs, scope, diag_);
    CheckIndexedPartSelectWidth(item->assign_lhs, scope, diag_);
  }
  if (is_proc && item->body) {
    CheckRealSelectStmt(item->body, var_types_, kOperands, diag_);
    CheckScalarSelectStmt(item->body, scalar_var_names_, diag_);
    CheckIndexedPartSelectWidthStmt(item->body, scope, diag_);
  }
}

void ReportForceOverMixture(std::string_view name, SourceLoc loc,
                            DiagEngine& diag) {
  diag.ErrorOnce(loc,
                 std::format("force or release applied to variable '{}', "
                             "which is assigned by a mixture of continuous "
                             "and procedural assignments",
                             name),
                 Subclause("10.6.2"));
}

static void ReportForceOverMixedAssignments(
    const std::unordered_map<std::string_view, SourceLoc>& force_targets,
    const std::unordered_map<std::string_view, SourceLoc>& cont_targets,
    const std::unordered_map<std::string_view, SourceLoc>& proc_targets,
    DiagEngine& diag) {
  for (const auto& [name, loc] : force_targets) {
    if (cont_targets.count(name) != 0 && proc_targets.count(name) != 0) {
      ReportForceOverMixture(name, loc, diag);
    }
  }
}

void Elaborator::ValidateMixedAssignments() {
  ReportForceOverMixedAssignments(force_release_targets_, cont_assign_targets_,
                                  proc_assign_targets_, diag_);
  for (const auto& [name, loc] : cont_assign_targets_) {
    if (proc_assign_targets_.find(name) != proc_assign_targets_.end()) {
      diag_.Error(loc,
                  std::format("variable '{}' has both continuous and "
                              "procedural assignments",
                              name),
                  Subclause("6.5"));
    }
  }
  for (const auto& [name, loc] : output_port_targets_) {
    if (cont_assign_targets_.find(name) != cont_assign_targets_.end()) {
      diag_.Error(loc,
                  std::format("variable '{}' driven by both output port and "
                              "continuous assignment",
                              name),
                  Subclause("6.5"));
    }
    if (var_init_names_.count(name) != 0) {
      diag_.Error(loc,
                  std::format("variable '{}' driven by output port has an "
                              "initializer",
                              name),
                  Subclause("6.5"));
    }
    if (proc_assign_targets_.find(name) != proc_assign_targets_.end()) {
      diag_.Error(loc,
                  std::format("variable '{}' driven by output port has "
                              "procedural assignments",
                              name),
                  Subclause("6.5"));
    }
  }
}

static bool NonAnsiPortIsVariable(const ModuleDecl* decl,
                                  std::string_view name) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->name == name)
      return true;
  }
  return false;
}

static bool InputPortIsVariable(const ModuleDecl* decl, const PortDecl& port) {
  if (decl->is_non_ansi_ports &&
      port.data_type.kind == DataTypeKind::kImplicit &&
      !port.has_explicit_var) {
    return NonAnsiPortIsVariable(decl, port.name);
  }
  return !port.data_type.is_net;
}

void Elaborator::ValidateInputPortAssignments(const ModuleDecl* decl) {
  bool is_checker = decl->decl_kind == ModuleDeclKind::kChecker;
  for (const auto& port : decl->ports) {
    if (port.direction != Direction::kInput) continue;
    bool port_is_var = InputPortIsVariable(decl, port);
    if (!port_is_var && !is_checker) continue;

    std::string msg =
        is_checker ? std::format(
                         "input formal argument '{}' cannot be modified "
                         "inside checker '{}'",
                         port.name, decl->name)
                   : std::format(
                         "variable '{}' is declared as an input port and "
                         "cannot be the target of an assignment",
                         port.name);
    Subclause subclause =
        is_checker ? Subclause("17.2") : Subclause("23.3.3.2");
    auto ca = cont_assign_targets_.find(port.name);
    if (ca != cont_assign_targets_.end()) {
      diag_.Error(ca->second, msg, subclause);
    }
    auto pa = proc_assign_targets_.find(port.name);
    if (pa != proc_assign_targets_.end()) {
      diag_.Error(pa->second, msg, subclause);
    }
  }
}

static void CheckDisableTargets(
    const Stmt* s,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kDisable && s->expr &&
      s->expr->kind == ExprKind::kIdentifier) {
    if (func_decls.count(s->expr->text) != 0) {
      diag.Error(s->range.start,
                 "a function cannot be the target of a disable statement",
                 Subclause("9.6.2"));
    }
  }
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckDisableTargets(sub, func_decls, diag); });
}

void Elaborator::ValidateDisableTargets(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      if (item->body) CheckDisableTargets(item->body, func_decls_, diag_);
    }
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      for (auto* s : item->func_body_stmts)
        CheckDisableTargets(s, func_decls_, diag_);
    }
  }
}

void Elaborator::ValidateProceduralNetAssign() {
  ReportProceduralNetTargets(proc_assign_targets_);
}

void Elaborator::ReportProceduralNetTargets(
    const std::unordered_map<std::string_view, SourceLoc>& targets) {
  for (const auto& [name, loc] : targets) {
    if (NamesNet(name, loc)) {
      diag_.Error(loc,
                  std::format("net '{}' cannot be the target of a "
                              "procedural assignment",
                              name),
                  Subclause("10.4"));
    }
  }
}

static bool IsAssocIndexTypeName(std::string_view name) {
  return name == "*" || name == "string" || name == "int" ||
         name == "integer" || name == "byte" || name == "shortint" ||
         name == "longint";
}

static bool DimsAreDynamicallySized(const std::vector<Expr*>& dims,
                                    bool* dynamic) {
  *dynamic = false;
  if (dims.empty()) return false;
  const Expr* dim = dims[0];
  if (dim == nullptr) {
    *dynamic = true;
    return true;
  }
  if (IsQueueDim(dim)) return true;
  return dim->kind == ExprKind::kIdentifier && IsAssocIndexTypeName(dim->text);
}

static bool DeclaresDynamicallySizedArray(const Stmt* s, bool* dynamic) {
  return DimsAreDynamicallySized(s->var_unpacked_dims, dynamic);
}

static void CollectProceduralDynamicNames(
    const Stmt* s, std::unordered_set<std::string_view>& dyn_names,
    std::unordered_set<std::string_view>& dynsized_names) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl || s->kind == StmtKind::kBlockItemDecl) {
    bool dynamic = false;
    if (DeclaresDynamicallySizedArray(s, &dynamic)) {
      dynsized_names.insert(s->var_name);
      if (dynamic) dyn_names.insert(s->var_name);
    }
  }
  ForEachChildStmt(s, [&dyn_names, &dynsized_names](Stmt* const& sub) {
    CollectProceduralDynamicNames(sub, dyn_names, dynsized_names);
  });
}

void ForEachItemAndGenerateDescendant(
    const ModuleItem* item, const std::function<void(const ModuleItem*)>& fn) {
  if (item == nullptr) return;
  fn(item);
  for (const auto* child : item->gen_body) {
    ForEachItemAndGenerateDescendant(child, fn);
  }
  ForEachItemAndGenerateDescendant(item->gen_else, fn);
  for (const auto& case_item : item->gen_case_items) {
    for (const auto* child : case_item.body) {
      ForEachItemAndGenerateDescendant(child, fn);
    }
  }
}

static void ReportDynamicLvalueAssign(
    const Stmt* s, const std::unordered_set<std::string_view>& dyn_names,
    DiagEngine& diag) {
  if (s->kind != StmtKind::kForce && s->kind != StmtKind::kAssign) return;
  if (s->lhs->kind != ExprKind::kSelect &&
      s->lhs->kind != ExprKind::kMemberAccess)
    return;
  if (dyn_names.count(LhsBaseName(s->lhs)) != 0) {
    diag.Error(s->range.start,
               "procedural continuous assignment to element of "
               "dynamic array",
               Subclause("6.21"));
  }
}

void CheckPcontDynamicArrayTarget(
    const Stmt* s, const std::unordered_set<std::string_view>& dyn_names,
    DiagEngine& diag) {
  if (!s) return;
  ReportDynamicLvalueAssign(s, dyn_names, diag);
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckPcontDynamicArrayTarget(sub, dyn_names, diag);
  });
}

static void CollectItemDynamicNames(
    const ModuleItem* item, std::unordered_set<std::string_view>& dyn_names,
    std::unordered_set<std::string_view>& dynsized_names) {
  bool dynamic = false;
  if (item->kind == ModuleItemKind::kVarDecl &&
      DimsAreDynamicallySized(item->unpacked_dims, &dynamic)) {
    dynsized_names.insert(item->name);
    if (dynamic) dyn_names.insert(item->name);
  }
}

void Elaborator::ValidateDynamicArrayNba(const ModuleDecl* decl) {
  const TypeShapeTables kShapeTables{typedefs_, td_array_dims_, class_names_};
  CheckNbaDynamicElements(decl, NbaDynamicTables{kShapeTables, unit_}, diag_);
  std::unordered_set<std::string_view> dyn_names;
  std::unordered_set<std::string_view> dynsized_names;
  for (const auto& [name, info] : var_array_info_) {
    if (info.is_dynamic) dyn_names.insert(name);
  }
  auto collect = [&dyn_names, &dynsized_names](const ModuleItem* item) {
    CollectItemDynamicNames(item, dyn_names, dynsized_names);
    CollectProceduralDynamicNames(item->body, dyn_names, dynsized_names);
    for (auto* s : item->func_body_stmts)
      CollectProceduralDynamicNames(s, dyn_names, dynsized_names);
  };
  for (const auto* item : decl->items) {
    ForEachItemAndGenerateDescendant(item, collect);
  }
  if (dyn_names.empty()) return;
  auto check = [&dyn_names, this](const ModuleItem* item) {
    if (item->body) CheckPcontDynamicArrayTarget(item->body, dyn_names, diag_);
    for (auto* s : item->func_body_stmts)
      CheckPcontDynamicArrayTarget(s, dyn_names, diag_);
  };
  for (const auto* item : decl->items) {
    ForEachItemAndGenerateDescendant(item, check);
  }
}

bool IsArrayQueryFunc(std::string_view callee) {
  return callee == "$left" || callee == "$right" || callee == "$low" ||
         callee == "$high" || callee == "$increment" || callee == "$size" ||
         callee == "$dimensions" || callee == "$unpacked_dimensions";
}

bool TypedefHasDynamicDim(const std::vector<Expr*>& dims) {
  for (const auto* d : dims) {
    if (d == nullptr) return true;
    if (d->kind == ExprKind::kIdentifier && (d->text == "$" || d->text == "*"))
      return true;
  }
  return false;
}

namespace {

void CheckArrayQueryOnDynamicTypeExpr(
    const Expr* e, const std::unordered_set<std::string_view>& dyn_types,
    DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSystemCall && IsArrayQueryFunc(e->callee) &&
      !e->args.empty() && e->args[0] &&
      e->args[0]->kind == ExprKind::kIdentifier &&
      dyn_types.count(e->args[0]->text) != 0) {
    diag.Error(e->range.start,
               std::format("array query function '{}' cannot be applied "
                           "directly to dynamically sized type '{}'",
                           e->callee, e->args[0]->text),
               Subclause("20.7"));
  }
  CheckArrayQueryOnDynamicTypeExpr(e->lhs, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->rhs, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->condition, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->true_expr, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->false_expr, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->base, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->index, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->index_end, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->repeat_count, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->with_expr, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(e->stream_range, dyn_types, diag);
  for (auto* a : e->args) CheckArrayQueryOnDynamicTypeExpr(a, dyn_types, diag);
  for (auto* el : e->elements)
    CheckArrayQueryOnDynamicTypeExpr(el, dyn_types, diag);
}

void CheckArrayQueryOnDynamicTypeStmt(
    const Stmt* s, const std::unordered_set<std::string_view>& dyn_types,
    DiagEngine& diag) {
  if (!s) return;
  CheckArrayQueryOnDynamicTypeExpr(s->condition, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(s->lhs, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(s->rhs, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(s->expr, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(s->delay, dyn_types, diag);
  CheckArrayQueryOnDynamicTypeExpr(s->var_init, dyn_types, diag);
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckArrayQueryOnDynamicTypeStmt(sub, dyn_types, diag);
  });
}

}  // namespace

void Elaborator::ValidateArrayQueryOnDynamicType(const ModuleDecl* decl) {
  std::unordered_set<std::string_view> dyn_types;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTypedef &&
        TypedefHasDynamicDim(item->unpacked_dims)) {
      dyn_types.insert(item->name);
    }
  }
  if (dyn_types.empty()) return;
  for (const auto* item : decl->items) {
    if (item->body)
      CheckArrayQueryOnDynamicTypeStmt(item->body, dyn_types, diag_);
    for (auto* s : item->func_body_stmts)
      CheckArrayQueryOnDynamicTypeStmt(s, dyn_types, diag_);
    CheckArrayQueryOnDynamicTypeExpr(item->init_expr, dyn_types, diag_);
  }
}

namespace {

bool IsNonIntegralSeedKind(DataTypeKind k) {
  return IsRealType(k) || k == DataTypeKind::kString;
}

void CheckRandomSeedExpr(const Expr* e, const TypeMap& types,
                         DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSystemCall && e->callee == "$random" &&
      !e->args.empty() && e->args[0]) {
    auto name = ExprIdent(e->args[0]);
    if (!name.empty()) {
      auto it = types.find(name);
      if (it != types.end() && IsNonIntegralSeedKind(it->second)) {
        diag.Error(
            e->range.start,
            "$random cannot take its seed from a variable that is not integral",
            Subclause("20.14.1"));
      }
    }
  }
  CheckRandomSeedExpr(e->lhs, types, diag);
  CheckRandomSeedExpr(e->rhs, types, diag);
  CheckRandomSeedExpr(e->condition, types, diag);
  CheckRandomSeedExpr(e->true_expr, types, diag);
  CheckRandomSeedExpr(e->false_expr, types, diag);
  CheckRandomSeedExpr(e->base, types, diag);
  CheckRandomSeedExpr(e->index, types, diag);
  CheckRandomSeedExpr(e->index_end, types, diag);
  CheckRandomSeedExpr(e->repeat_count, types, diag);
  CheckRandomSeedExpr(e->with_expr, types, diag);
  CheckRandomSeedExpr(e->stream_range, types, diag);
  for (auto* a : e->args) CheckRandomSeedExpr(a, types, diag);
  for (auto* el : e->elements) CheckRandomSeedExpr(el, types, diag);
}

void CheckRandomSeedStmt(const Stmt* s, const TypeMap& types,
                         DiagEngine& diag) {
  if (!s) return;
  CheckRandomSeedExpr(s->condition, types, diag);
  CheckRandomSeedExpr(s->lhs, types, diag);
  CheckRandomSeedExpr(s->rhs, types, diag);
  CheckRandomSeedExpr(s->expr, types, diag);
  CheckRandomSeedExpr(s->delay, types, diag);
  CheckRandomSeedExpr(s->var_init, types, diag);
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckRandomSeedStmt(sub, types, diag); });
}

}  // namespace

void Elaborator::ValidateRandomSeedType(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->body) CheckRandomSeedStmt(item->body, var_types_, diag_);
    for (auto* s : item->func_body_stmts)
      CheckRandomSeedStmt(s, var_types_, diag_);
    CheckRandomSeedExpr(item->init_expr, var_types_, diag_);
  }
}

}  // namespace delta
