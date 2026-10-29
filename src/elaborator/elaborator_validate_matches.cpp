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

// §10.9 requires positional notation of every assignment pattern a left-hand
// expression holds, and A.8.5 lets each element of a concatenation target or
// of a pattern target be a pattern again, so the elements are read in turn.
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

// §10.9 puts no condition on where the assignment whose left-hand side is a
// pattern stands, so every position a statement holds a statement in is a
// position the rule reaches. ForEachChildStmt in elaborator_validate_internal.h
// states those positions once for the whole elaborator, which is why the list
// is not written out again here.
//
// The visitor takes `Stmt* const&` because `s` is a `const Stmt*`, which is how
// ForEachChildStmt lets a walk that only reads the tree share its list with the
// walks that rewrite it. Nothing stops early, since §10.9 is broken as many
// times as a source writes a keyed pattern on the left of an assignment.
static void WalkStmtsForLhsPatternKeys(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckLhsPatternNamedKeys(s->lhs, diag);
  }
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { WalkStmtsForLhsPatternKeys(sub, diag); });
}

// §10.4, §10.6.2 and §10.9 state their rules of a procedural statement
// wherever it stands, and the body of a task or function is such a place.
// §6.5 weighs a subroutine's procedural assignment to a variable against a
// continuous one as it weighs a process's, so the variables are recorded with
// the processes' targets; a net it writes is reported here, once. A class
// method defined out of its class writes the class's properties, which no
// module name stands for.
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
  // §6.5 counts a procedural assign as a procedural assignment as well; one
  // naming a net was reported just above, under §10.6.1.
  CollectProcContAssignTargets(item->func_args, item->func_body_stmts, targets);
  for (const auto& [name, loc] : targets)
    if (!NamesNet(name, loc)) proc_assign_targets_.emplace(name, loc);
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
  bool is_proc = IsProceduralItemKind(item->kind);
  if (is_proc && item->body) {
    CollectProcTargets({}, {item->body}, proc_assign_targets_);
    // §6.5 counts a procedural assign as a procedural assignment as well. One
    // naming a net is §10.6.1's to report, so the variables alone join.
    std::unordered_map<std::string_view, SourceLoc> assigned;
    CollectProcContAssignTargets({}, {item->body}, assigned);
    std::erase_if(assigned, [this](const auto& target) {
      return NamesNet(target.first, target.second);
    });
    proc_assign_targets_.merge(assigned);
    CollectForceReleaseTargets(item->body, force_release_targets_);

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
  // §10.8 makes a continuous assignment an assignment-like context, so a
  // pattern on its left-hand side is positional too (§10.9).
  if (item->kind == ModuleItemKind::kContAssign)
    CheckLhsPatternNamedKeys(item->assign_lhs, diag_);
  ValidateEdgeOnReal(item);
  ValidateChandleContAssign(item);
  ValidateChandleSensitivity(item);
  ValidateVirtualInterfaceContAssign(item);
  ValidateVirtualInterfaceSensitivity(item);
  ValidateClassHandleContAssign(item);

  // §6.3.2.2's rule that a drive strength needs an assignment in the same
  // statement is not checked here. This walk reaches the module's own items and
  // stops, so a net declared inside a generate block escaped it; the rule now
  // sits in ElaborateNetDecl, which every elaborated net declaration passes
  // through.

  CheckHighzStrengthPair(item, diag_);
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

// §10.6.2 (printed page 257): force and release may not be applied to a
// variable assigned by a mixture of continuous and procedural assignments. This
// is a second rule over a source §6.5 already rejects, and it names the
// statement the author has to change rather than the assignment, so both
// reports are emitted and neither suppresses the other. A force can never
// itself create the mixture it may not be applied over: §6.5 (printed page 91)
// makes a force statement neither a continuous nor a procedural assignment,
// which is why CollectProcTargets counts only StmtKind::kBlockingAssign and
// StmtKind::kNonblockingAssign.
static void ReportForceOverMixedAssignments(
    const std::unordered_map<std::string_view, SourceLoc>& force_targets,
    const std::unordered_map<std::string_view, SourceLoc>& cont_targets,
    const std::unordered_map<std::string_view, SourceLoc>& proc_targets,
    DiagEngine& diag) {
  for (const auto& [name, loc] : force_targets) {
    if (cont_targets.count(name) != 0 && proc_targets.count(name) != 0) {
      diag.Error(loc,
                 std::format("force or release applied to variable '{}', which "
                             "is assigned by a mixture of continuous and "
                             "procedural assignments",
                             name),
                 Subclause("10.6.2"));
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

// Whether a port declared in the non-ANSI style is of a variable kind.
//
// Syntax 23-3 gives the direction declaration two alternatives, `input
// net_port_type list_of_port_identifiers` and `input variable_port_type
// list_of_variable_identifiers`, and a declaration that names no type at all
// matches the net one -- a net_port_type admits an implicit data type where a
// variable_port_type does not. §23.2.2.1 then allows such a port to be declared
// again in a net or variable declaration, and it is that second declaration, in
// the module body, that can make the port a variable. So the port is a variable
// exactly when the body says so.
static bool NonAnsiPortIsVariable(const ModuleDecl* decl,
                                  std::string_view name) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->name == name)
      return true;
  }
  return false;
}

// Whether an input port is of a variable kind, for the §23.3.3.2 rule that
// only variable input ports may not be assigned. A net input port driven from
// inside the module falls under the net rules (§23.3.3.3) instead.
//
// A non-ANSI direction declaration that named no type is marked a net, as
// §23.2.2.1 makes it until the body declares it again, so the body is read
// before that mark: `input a; reg a;` is a variable the rule covers, while an
// ordinary `input a;` stays a net whose continuous assignment §23.3.3.1 meets
// with coercion to inout and a warning. `input var a;` is a variable by its
// own declaration.
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
    // §17.2: a checker shall not modify any of its input formal arguments, and
    // a checker input formal is net-typed, so the variable-only exception above
    // does not apply inside a checker body.
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
    // The rule broken is the one the message names: §17.2 for a checker input
    // formal, and §23.3.3.2's variable port connection rule for a module,
    // interface or program input port.
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

// §9.6.2 bars a disable statement naming a function wherever the disable is
// written. ForEachChildStmt in elaborator_validate_internal.h states those
// positions once for the whole elaborator, which is why the list is not written
// out again here.
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

// §10.4 (printed page 251): a procedural assignment's left-hand side is a
// variable, and a net is none.
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

// §7.8.1 lists the index types an associative array may be keyed by, and the
// wildcard `*` of §7.8.1. A dimension written as a bare name is one of these or
// it is §7.4.2's size form given by a parameter, and only the names listed here
// are read as an index type: an unrecognised one is left as a size, so a
// declaration this cannot classify goes unreported rather than reported
// wrongly. A class-keyed or typedef-keyed associative array is therefore among
// the ones left, which is where the module-item path -- which has the
// elaborated variable rather than the dimension text -- still answers and this
// does not.
static bool IsAssocIndexTypeName(std::string_view name) {
  return name == "*" || name == "string" || name == "int" ||
         name == "integer" || name == "byte" || name == "shortint" ||
         name == "longint";
}

// §6.21's dynamically sized array variables are the three §7.4 admits whose
// size the declaration does not fix, and the first unpacked dimension is what
// says which: `[]` reaches the parser as no dimension expression at all, `[$]`
// and `[$:N]` are §7.10's queue, and an index type is §7.8's associative array.
// `*dynamic` is set for the dynamic array alone, which is the narrower of the
// two sets the caller keeps.
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

// The dynamically sized arrays a procedure declares in its own scope. A
// declaration inside a begin-end block, a loop or fork body, or a subroutine
// body is a Stmt rather than a ModuleItem, so it never reaches
// Elaborator::ElaborateVarDecl and never enters var_array_info_, and §6.21's
// rule went unenforced for every one of them: `initial begin int q[$]; q[0] <=
// 1; end` elaborated clean where the same queue declared among the module's
// items is rejected.
//
// A bare name set is all this rule needs -- it asks whether any `q` in scope is
// dynamically sized, and every candidate is forbidden as a nonblocking element
// target -- so the collision that would come of keying var_array_info_ itself
// by an unqualified block-scope name, and of handing the wrong `q` to the rules
// that decide a diagnostic from the shape they find, does not arise here.
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

// §27.6 makes a generate block's declarations declarations of the module, and
// §27.4 and §27.5 put the construct's contents in its own nested lists rather
// than beside the module's other items: a kGenerateFor, kGenerateIf or
// kGenerateCase item carries them in gen_body, gen_else and the case items'
// bodies, and its own `body` is null and its func_body_stmts empty. A walk of
// decl->items alone therefore never reaches a statement written inside one, and
// §6.21's rule went unenforced there: `if (1) begin : g int q[$]; initial q[0]
// <= 1; end` elaborated clean where the same two lines at module scope are
// rejected. Visits the item and every item a generate construct holds under it.
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

// §6.21 (printed page 134), first sentence: no continuous or procedural
// continuous assignment may write an element of a dynamically sized array
// variable, and `b[2].x` falls under it, because the name is a member while
// the object the write lands in is the element `b[2]`, and writing part of an
// element is writing it. The nonblocking half of the sentence, which §10.4.2
// states for itself, is CheckNbaDynamicElements in nba_dynamic_element.cpp.
static void ReportDynamicLvalueAssign(
    const Stmt* s, const std::unordered_set<std::string_view>& dyn_names,
    DiagEngine& diag) {
  if (s->kind != StmtKind::kForce && s->kind != StmtKind::kAssign) return;
  // The kind gate rather than the walk is what confines this to a part of a
  // dynamic array: a bare identifier lvalue is a write to the whole object,
  // which the clause permits, and LhsBaseName answers the same name for it as
  // for a select of it.
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

// The dynamically sized arrays one item declares. A declaration among the
// module's own items has already entered var_array_info_ by way of
// Elaborator::ElaborateVarDecl; one inside a generate construct has not, since
// §27 expands the construct after this rule runs, so its dimensions are read
// from the declaration itself. §6.21 asks only whether a name in scope is
// dynamically sized, which the declaration says on its own.
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
  // The two lists below are the ones the check itself walks, so the names a
  // procedure declares are collected from the same trees the offending
  // statement is found in, and one pass over each serves both.
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

// §20.7 treats a typedef as dynamically sized when one of its unpacked
// dimensions is a dynamic array ([], parsed as a null dimension), a queue
// ([$], a "$" identifier dimension), or a wildcard associative array ([*]).
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
  // A bare identifier first argument that names a dynamically sized typedef is
  // the type identifier itself, not an object of that type; querying it has no
  // defined extent.
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

// §20.7 bars a direct query on a dynamically sized type identifier wherever the
// query is written. ForEachChildStmt in elaborator_validate_internal.h states
// those positions once for the whole elaborator, which is why the list is not
// written out again here.
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
  // §20.7: the array query functions may not be used directly on a dynamically
  // sized type identifier. Collect such typedef names, then reject any direct
  // query on one.
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

// §20.14.1 lets $random take its seed only from an integral variable. A real
// or string variable cannot hold the integral seed state, so a seed naming one
// is rejected. Other clearly integral kinds (vectors, enums, packed structs)
// are left alone to avoid false positives on legitimate seeds.
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

// §20.14.1's rule on the seed argument holds wherever a $random call is
// written. ForEachChildStmt in elaborator_validate_internal.h states those
// positions once for the whole elaborator, which is why the list is not written
// out again here.
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
  // §20.14.1: enforce that any $random seed argument naming a module variable
  // refers to an integral variable.
  for (const auto* item : decl->items) {
    if (item->body) CheckRandomSeedStmt(item->body, var_types_, diag_);
    for (auto* s : item->func_body_stmts)
      CheckRandomSeedStmt(s, var_types_, diag_);
    CheckRandomSeedExpr(item->init_expr, var_types_, diag_);
  }
}

}  // namespace delta
