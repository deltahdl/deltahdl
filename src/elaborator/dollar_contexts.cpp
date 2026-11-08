#include "elaborator/dollar_contexts.h"

#include <algorithm>
#include <format>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/declared_types.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/queue_dim.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

bool AnyScalarChildContainsDollar(const Expr* e) {
  const Expr* const kChildren[] = {
      e->lhs,        e->rhs,          e->condition,   e->true_expr,
      e->false_expr, e->base,         e->index,       e->index_end,
      e->with_expr,  e->stream_range, e->repeat_count};
  for (const Expr* c : kChildren) {
    if (ContainsDollar(c)) return true;
  }
  return false;
}

}  // namespace

bool IsLoneDollar(const Expr* e) {
  return e->kind == ExprKind::kIdentifier && e->text == "$";
}

bool ContainsDollar(const Expr* e) {
  if (e == nullptr) return false;
  if (IsLoneDollar(e)) return true;
  if (AnyScalarChildContainsDollar(e)) return true;
  for (const Expr* a : e->args)
    if (ContainsDollar(a)) return true;
  for (const Expr* el : e->elements)
    if (ContainsDollar(el)) return true;
  return false;
}

namespace {

struct QueueContextScan {
  const std::unordered_set<std::string_view>& unbounded;
  const std::unordered_set<std::string_view>& queues;
  DiagEngine& diag;
};

}  // namespace

static bool NamesUnboundedParam(const Expr* e, const QueueContextScan& scan) {
  return e->kind == ExprKind::kIdentifier && e->scope_prefix.empty() &&
         scan.unbounded.count(e->text) != 0;
}

static void Report(const Expr* param, const QueueContextScan& scan) {
  scan.diag.Error(param->range.start,
                  std::format("parameter '{}' holds '$', which a queue context "
                              "does not permit",
                              param->text),
                  Subclause("6.20.7"));
}

static void ReportUnboundedParamsIn(const Expr* e,
                                    const QueueContextScan& scan) {
  if (e == nullptr) return;
  if (NamesUnboundedParam(e, scan)) Report(e, scan);
  ForEachExprChild(
      e, [&scan](const Expr* child) { ReportUnboundedParamsIn(child, scan); });
}

static void CheckDims(const std::vector<Expr*>& dims,
                      const QueueContextScan& scan) {
  for (const Expr* dim : dims) {
    if (IsQueueDim(dim)) {
      ReportUnboundedParamsIn(dim->rhs, scan);
    } else if (dim != nullptr && NamesUnboundedParam(dim, scan)) {
      Report(dim, scan);
    }
  }
}

static void CheckExpr(const Expr* e, const QueueContextScan& scan) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kSelect && e->base != nullptr &&
      e->base->kind == ExprKind::kIdentifier &&
      scan.queues.count(e->base->text) != 0) {
    ReportUnboundedParamsIn(e->index, scan);
    ReportUnboundedParamsIn(e->index_end, scan);
  }
  ForEachExprChild(e, [&scan](const Expr* child) { CheckExpr(child, scan); });
}

static void CheckStmt(const Stmt* s, const QueueContextScan& scan) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) CheckDims(s->var_unpacked_dims, scan);
  ForEachChildExpr(s, [&scan](const Expr* e) { CheckExpr(e, scan); });
  ForEachChildStmt(s, [&scan](Stmt* const& sub) { CheckStmt(sub, scan); });
}

void CheckUnboundedParamsInQueueContexts(
    const ModuleDecl* decl,
    const std::unordered_set<std::string_view>& unbounded,
    const std::unordered_set<std::string_view>& queues, DiagEngine& diag) {
  if (unbounded.empty()) return;
  const QueueContextScan kScan{unbounded, queues, diag};
  for (const ModuleItem* item : decl->items) {
    CheckDims(item->unpacked_dims, kScan);
    CheckExpr(item->init_expr, kScan);
    CheckExpr(item->assign_lhs, kScan);
    CheckExpr(item->assign_rhs, kScan);
    CheckStmt(item->body, kScan);
    for (const Stmt* s : item->func_body_stmts) CheckStmt(s, kScan);
  }
}

static void ReportDollar(const Expr* e, DiagEngine& diag) {
  diag.Error(e->range.start,
             "'$' may stand only in a queue's dimension or select, a value "
             "range's bound, a cycle delay range's upper bound, a sequence, "
             "property or checker argument, or a parameter's value",
             Subclause("6.20.7"));
}

bool ReportDollarsIn(const Expr* e, DiagEngine& diag) {
  if (e == nullptr) return false;
  if (IsLoneDollar(e)) {
    ReportDollar(e, diag);
    return true;
  }
  bool reported = false;
  ForEachExprChild(e, [&diag, &reported](const Expr* child) {
    reported = ReportDollarsIn(child, diag) || reported;
  });
  return reported;
}

namespace {

using NameSet = std::unordered_set<std::string_view>;

struct DollarScope {
  const DollarScope* outer = nullptr;
  NameSet non_queues;
  NameSet others;
};

struct DollarScan {
  const DollarScope& scope;
  const NameSet& dollar_takers;
  DiagEngine& diag;
};

}  // namespace

static void NoteDeclaredName(std::string_view name, const DataType& type,
                             const std::vector<Expr*>& dims,
                             DollarScope& scope) {
  const bool kFixedFirst = !dims.empty() && !IsQueueDim(dims[0]);
  const bool kPlain = dims.empty() && type.kind != DataTypeKind::kNamed &&
                      type.type_ref_expr == nullptr;
  (kFixedFirst || kPlain ? scope.non_queues : scope.others).insert(name);
}

static bool NamesNonQueue(const DollarScope* scope, std::string_view name) {
  for (; scope != nullptr; scope = scope->outer) {
    if (scope->non_queues.count(name) != 0) return true;
    if (scope->others.count(name) != 0) return false;
  }
  return false;
}

static void NoteItemNames(const std::vector<ModuleItem*>& items,
                          DollarScope& scope) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kVarDecl ||
        item->kind == ModuleItemKind::kNetDecl) {
      NoteDeclaredName(item->name, item->data_type, item->unpacked_dims, scope);
    }
  }
}

static void NoteLocalNames(const Stmt* s, DollarScope& scope) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) {
    NoteDeclaredName(s->var_name, s->var_decl_type, s->var_unpacked_dims,
                     scope);
  }
  ForEachChildStmt(s,
                   [&scope](Stmt* const& sub) { NoteLocalNames(sub, scope); });
}

static void AddDollarTakerNames(const std::vector<ModuleItem*>& items,
                                NameSet& names) {
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kSequenceDecl ||
        item->kind == ModuleItemKind::kPropertyDecl) {
      names.insert(item->name);
    }
    const ModuleDecl* nested = item->nested_module_decl;
    if (nested != nullptr && nested->decl_kind == ModuleDeclKind::kChecker)
      names.insert(nested->name);
  }
}

static NameSet UnitDollarTakers(const CompilationUnit& unit) {
  NameSet names;
  AddDollarTakerNames(unit.cu_items, names);
  for (const PackageDecl* pkg : unit.packages)
    AddDollarTakerNames(pkg->items, names);
  for (const ModuleDecl* checker : unit.checkers) names.insert(checker->name);
  return names;
}

static bool SelectsANonQueue(const Expr* select, const DollarScan& scan) {
  const Expr* base = select->base;
  return base != nullptr && base->kind == ExprKind::kIdentifier &&
         NamesNonQueue(&scan.scope, base->text);
}

static void CheckDollarOperand(const Expr* e, const DollarScan& scan);

static void CheckConstraintItems(const std::vector<ConstraintItem*>& items,
                                 const DollarScan& scan);

static void CheckRangeBound(const Expr* bound, const DollarScan& scan) {
  if (bound != nullptr && IsLoneDollar(bound)) return;
  CheckDollarOperand(bound, scan);
}

static bool IsToleranceRange(const Expr* range) {
  return range->op == TokenKind::kPlusSlashMinus ||
         range->op == TokenKind::kPlusPercentMinus;
}

static void CheckSelect(const Expr* e, const DollarScan& scan) {
  if (e->base == nullptr && !IsToleranceRange(e)) {
    CheckRangeBound(e->index, scan);
    CheckRangeBound(e->index_end, scan);
    return;
  }
  CheckDollarOperand(e->base, scan);
  if (e->base == nullptr || SelectsANonQueue(e, scan)) {
    CheckDollarOperand(e->index, scan);
    CheckDollarOperand(e->index_end, scan);
  }
}

static void CheckDollarOperand(const Expr* e, const DollarScan& scan) {
  if (e == nullptr) return;
  if (e->inline_constraint != nullptr)
    CheckConstraintItems(e->inline_constraint->constraint_items, scan);
  if (IsQueueDim(e)) {
    ReportDollar(e, scan.diag);
    return;
  }
  if (e->kind == ExprKind::kSelect) {
    CheckSelect(e, scan);
    return;
  }
  if (e->kind == ExprKind::kCall && scan.dollar_takers.count(e->callee) != 0)
    return;
  ForEachExprChild(
      e, [&scan](const Expr* child) { CheckDollarOperand(child, scan); });
}

static void CheckDistItem(const ConstraintDistItem& item,
                          const DollarScan& scan) {
  CheckDollarOperand(item.weight, scan);
  if (item.tolerance != nullptr) {
    CheckDollarOperand(item.lo, scan);
    CheckDollarOperand(item.tolerance, scan);
  } else if (item.is_range) {
    CheckRangeBound(item.lo, scan);
    CheckRangeBound(item.hi, scan);
  } else {
    CheckDollarOperand(item.value, scan);
  }
}

static void CheckConstraintItems(const std::vector<ConstraintItem*>& items,
                                 const DollarScan& scan) {
  for (const ConstraintItem* item : items) {
    CheckDollarOperand(item->expr, scan);
    for (const ConstraintDistItem& dist : item->dist) CheckDistItem(dist, scan);
    for (const Expr* e : item->exprs) CheckDollarOperand(e, scan);
    CheckConstraintItems(item->body, scan);
    CheckConstraintItems(item->else_body, scan);
  }
}

static void CheckUnpackedDims(const std::vector<Expr*>& dims,
                              const DollarScan& scan) {
  for (const Expr* dim : dims) {
    CheckDollarOperand(IsQueueDim(dim) ? dim->rhs : dim, scan);
  }
}

static void CheckDeclaredDims(const DataType& type,
                              const std::vector<Expr*>& unpacked_dims,
                              const DollarScan& scan) {
  CheckDollarOperand(type.packed_dim_left, scan);
  CheckDollarOperand(type.packed_dim_right, scan);
  for (const auto& [left, right] : type.extra_packed_dims) {
    CheckDollarOperand(left, scan);
    CheckDollarOperand(right, scan);
  }
  CheckUnpackedDims(unpacked_dims, scan);
}

static void CheckDollarStmt(const Stmt* s, const DollarScan& scan) {
  if (s == nullptr) return;
  const std::vector<Expr*>& dims = s->var_unpacked_dims;
  ForEachChildExpr(s, [&scan, &dims](const Expr* e) {
    if (std::ranges::find(dims, e) == dims.end()) CheckDollarOperand(e, scan);
  });
  ForEachChildStmt(s,
                   [&scan](Stmt* const& sub) { CheckDollarStmt(sub, scan); });
}

static void CheckProcedure(const Stmt* body, const DollarScan& outer) {
  DollarScope scope;
  scope.outer = &outer.scope;
  NoteLocalNames(body, scope);
  CheckDollarStmt(body, {scope, outer.dollar_takers, outer.diag});
}

static void CheckSubroutine(const ModuleItem* item, const DollarScan& outer) {
  DollarScope scope;
  scope.outer = &outer.scope;
  for (const FunctionArg& arg : item->func_args) {
    CheckDollarOperand(arg.default_value, outer);
    NoteDeclaredName(arg.name, arg.data_type, arg.unpacked_dims, scope);
  }
  for (const Stmt* s : item->func_body_stmts) NoteLocalNames(s, scope);
  const DollarScan kInner{scope, outer.dollar_takers, outer.diag};
  for (const Stmt* s : item->func_body_stmts) CheckDollarStmt(s, kInner);
}

static void CheckInstanceActuals(const ModuleItem* item,
                                 const DollarScan& scan) {
  if (scan.dollar_takers.count(item->inst_module) != 0) return;
  for (const auto& [name, actual] : item->inst_ports)
    CheckDollarOperand(actual, scan);
}

static void CheckDollarItems(const std::vector<ModuleItem*>& items,
                             const DollarScan& outer);

static void CheckGenerate(const ModuleItem* item, const DollarScan& scan) {
  CheckDollarStmt(item->gen_init, scan);
  CheckDollarStmt(item->gen_step, scan);
  for (const ModuleItem* arm = item; arm != nullptr; arm = arm->gen_else) {
    CheckDollarOperand(arm->gen_cond, scan);
    CheckDollarItems(arm->gen_body, scan);
  }
  for (const GenerateCaseItem& arm : item->gen_case_items) {
    for (const Expr* pattern : arm.patterns) CheckDollarOperand(pattern, scan);
    CheckDollarItems(arm.body, scan);
  }
}

static void CheckDollarClass(const ClassDecl* cls, const DollarScan& outer);

static void CheckDollarItem(const ModuleItem* item, const DollarScan& scan) {
  switch (item->kind) {
    case ModuleItemKind::kVarDecl:
      CheckDollarOperand(item->init_expr, scan);
      break;
    case ModuleItemKind::kNetDecl:
      CheckDollarOperand(item->init_expr, scan);
      CheckDeclaredDims(item->data_type, item->unpacked_dims, scan);
      break;
    case ModuleItemKind::kModuleInst:
      CheckInstanceActuals(item, scan);
      break;
    default:
      for (const auto& [target, value] : item->defparam_assigns)
        CheckDollarOperand(value, scan);
      break;
  }
  CheckDollarOperand(item->assign_lhs, scan);
  CheckDollarOperand(item->assign_rhs, scan);
  CheckProcedure(item->body, scan);
  CheckSubroutine(item, scan);
  CheckGenerate(item, scan);
  if (item->class_decl != nullptr) CheckDollarClass(item->class_decl, scan);
}

static void CheckDollarClass(const ClassDecl* cls, const DollarScan& outer) {
  DollarScope scope;
  scope.outer = &outer.scope;
  for (const ClassMember* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty)
      NoteDeclaredName(m->name, m->data_type, m->unpacked_dims, scope);
  }
  const DollarScan kScan{scope, outer.dollar_takers, outer.diag};
  for (const Expr* arg : cls->extends_args) CheckDollarOperand(arg, kScan);
  for (const ClassMember* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty && !m->is_param)
      CheckDollarOperand(m->init_expr, kScan);
    if (m->method != nullptr) CheckDollarItem(m->method, kScan);
    CheckConstraintItems(m->constraint_items, kScan);
    if (m->nested_class != nullptr) CheckDollarClass(m->nested_class, kScan);
  }
}

static void CheckDollarItems(const std::vector<ModuleItem*>& items,
                             const DollarScan& outer) {
  DollarScope scope;
  scope.outer = &outer.scope;
  NoteItemNames(items, scope);
  const DollarScan kScan{scope, outer.dollar_takers, outer.diag};
  for (const ModuleItem* item : items) {
    CheckDollarItem(item, kScan);
    ForEachItemDeclaredType(item, [&kScan](const DeclaredType& declared) {
      CheckDeclaredDims(declared.type, declared.unpacked_dims, kScan);
    });
  }
}

void CheckDollarOperands(const ModuleDecl* decl, const CompilationUnit& unit,
                         DiagEngine& diag) {
  NameSet takers = UnitDollarTakers(unit);
  AddDollarTakerNames(decl->items, takers);
  DollarScope ports;
  for (const PortDecl& port : decl->ports)
    NoteDeclaredName(port.name, port.data_type, port.unpacked_dims, ports);
  const DollarScan kScan{ports, takers, diag};
  for (const PortDecl& port : decl->ports)
    CheckDeclaredDims(port.data_type, port.unpacked_dims, kScan);
  CheckDollarItems(decl->items, kScan);
}

void CheckUnitDollarOperands(const CompilationUnit& unit, DiagEngine& diag) {
  const NameSet kTakers = UnitDollarTakers(unit);
  const DollarScope kRoot;
  const DollarScan kPackageScan{kRoot, kTakers, diag};
  for (const PackageDecl* pkg : unit.packages)
    CheckDollarItems(pkg->items, kPackageScan);
  DollarScope unit_scope;
  NoteItemNames(unit.cu_items, unit_scope);
  const DollarScan kScan{unit_scope, kTakers, diag};
  CheckDollarItems(unit.cu_items, kScan);
  for (const ClassDecl* cls : unit.classes) {
    CheckDollarClass(cls, kScan);
    ForEachClassDeclaredType(cls, [&kScan](const DeclaredType& declared) {
      CheckDeclaredDims(declared.type, declared.unpacked_dims, kScan);
    });
  }
}

}  // namespace delta
