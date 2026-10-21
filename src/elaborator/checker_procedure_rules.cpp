#include "elaborator/checker_procedure_rules.h"

#include <algorithm>
#include <format>
#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/assertion_walk.h"
#include "elaborator/concurrent_assertion_expr.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/net_data_type.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

using NameSet = std::unordered_set<std::string_view>;

// The names of the items of `kind` the checker body declares.
NameSet DeclaredNames(const ModuleDecl* decl, ModuleItemKind kind) {
  NameSet names;
  for (const auto* item : decl->items) {
    if (item->kind == kind && !item->name.empty()) names.insert(item->name);
  }
  return names;
}

// §17.6: a declaration in a checker procedure whose type names one of the
// checker's covergroups, `automatic cg cg_1 = new();`, instantiates it there.
void WalkForCovergroupInstances(const Stmt* s, const NameSet& covergroups,
                                DiagEngine& diag) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl &&
      covergroups.count(s->var_decl_type.type_name) != 0) {
    diag.Error(s->range.start,
               std::format("covergroup '{}' cannot be instantiated in a "
                           "procedure of a checker; instantiate it in the "
                           "checker body",
                           s->var_decl_type.type_name),
               Subclause("17.6"));
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkForCovergroupInstances(sub, covergroups, diag);
  });
}

// The variable an assignment target writes, its selects and members
// stripped.
const Expr* TargetRoot(const Expr* e) {
  while (e->kind == ExprKind::kSelect || e->kind == ExprKind::kMemberAccess) {
    e = e->kind == ExprKind::kSelect ? e->base : e->lhs;
  }
  return e;
}

// §16.6: whether the function `fn` writes a variable other than its own
// formals, its locals and its result, which is a side effect; and, through
// `keeps_state`, whether it holds a value from one call to the next, a local
// whose declaration initializes it once where the local is static.
bool HasSideEffect(const ModuleItem* fn, bool& keeps_state) {
  NameSet own{fn->name};
  for (const FunctionArg& arg : fn->func_args) own.insert(arg.name);
  keeps_state = false;
  ForEachProceduralStmt(fn, [&](const Stmt* s) {
    if (s->kind != StmtKind::kVarDecl) return;
    own.insert(s->var_name);
    bool is_static = !fn->is_automatic || s->var_is_static;
    if (is_static && s->var_init != nullptr) keeps_state = true;
  });
  bool writes = false;
  ForEachProceduralStmt(fn, [&](const Stmt* s) {
    if (s->kind != StmtKind::kBlockingAssign &&
        s->kind != StmtKind::kNonblockingAssign) {
      return;
    }
    const Expr* root = TargetRoot(s->lhs);
    if (root->kind == ExprKind::kIdentifier && own.count(root->text) == 0) {
      writes = true;
    }
  });
  return writes;
}

// §17.8: each call in `e` of one of the functions `writers` names, which
// write an argument back, or `impure` names, which keep state or have a side
// effect.
void ReportWritingCalls(const Expr* e, const NameSet& writers,
                        const NameSet& impure, DiagEngine& diag) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kCall && writers.count(e->callee) != 0) {
    diag.Error(e->range.start,
               std::format("function '{}' has an output, inout or ref "
                           "argument and cannot be called on the right-hand "
                           "side of a checker variable assignment",
                           e->callee),
               Subclause("17.8"));
  }
  if (e->kind == ExprKind::kCall && impure.count(e->callee) != 0) {
    diag.Error(e->range.start,
               std::format("function '{}' keeps state or has a side effect "
                           "and cannot be called on the right-hand side of a "
                           "checker variable assignment",
                           e->callee),
               Subclause("17.8"));
  }
  ForEachExprChild(e, [&](const Expr* child) {
    ReportWritingCalls(child, writers, impure, diag);
  });
}

void WalkForWritingCalls(const Stmt* s, const NameSet& writers,
                         const NameSet& impure, DiagEngine& diag) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    ReportWritingCalls(s->rhs, writers, impure, diag);
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkForWritingCalls(sub, writers, impure, diag);
  });
}

}  // namespace

// §16.6's kinds of argument, which §17.8 applies to a function called on a
// checker variable's right-hand side; a formal written without a direction
// takes the one before it, the first input (§13.3).
bool HasArgumentWrittenBack(const ModuleItem* fn) {
  Direction dir = Direction::kInput;
  for (const FunctionArg& arg : fn->func_args) {
    if (arg.direction != Direction::kNone) dir = arg.direction;
    FunctionArgKind kind = FunctionArgKind::kInput;
    if (dir == Direction::kOutput) kind = FunctionArgKind::kOutput;
    if (dir == Direction::kInout) kind = FunctionArgKind::kInout;
    if (dir == Direction::kRef) {
      kind = arg.is_const ? FunctionArgKind::kConstRef : FunctionArgKind::kRef;
    }
    if (!FunctionArgKindAllowedInAssertionExpr(kind)) return true;
  }
  return false;
}

bool FunctionIsImpure(const ModuleItem* fn) {
  bool keeps_state = false;
  bool side_effect = HasSideEffect(fn, keeps_state);
  return !FunctionEligibleInAssertionExpr(fn->is_automatic, !keeps_state,
                                          !side_effect);
}

void ValidateCheckerProcedureCovergroups(const ModuleDecl* decl,
                                         DiagEngine& diag) {
  if (decl->decl_kind != ModuleDeclKind::kChecker) return;
  NameSet covergroups = DeclaredNames(decl, ModuleItemKind::kCovergroupDecl);
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      WalkForCovergroupInstances(item->body, covergroups, diag);
    }
  }
}

void ValidateCheckerAssignmentCalls(const ModuleDecl* decl, DiagEngine& diag) {
  if (decl->decl_kind != ModuleDeclKind::kChecker) return;
  NameSet writers;
  NameSet impure;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kFunctionDecl) continue;
    if (HasArgumentWrittenBack(item)) writers.insert(item->name);
    if (FunctionIsImpure(item)) impure.insert(item->name);
  }
  // A continuous assignment is left to §13.4, which bars such a function
  // from one wherever it is written.
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      WalkForWritingCalls(item->body, writers, impure, diag);
    }
  }
}

void ValidateCheckerFormalDefaults(const ModuleDecl* decl, DiagEngine& diag) {
  if (decl->decl_kind != ModuleDeclKind::kChecker) return;
  for (const PortDecl& port : decl->ports) {
    bool aggregate = (port.data_type.kind == DataTypeKind::kStruct ||
                      port.data_type.kind == DataTypeKind::kUnion) &&
                     !port.data_type.is_packed;
    if (port.default_value == nullptr ||
        (port.unpacked_dims.empty() && !aggregate)) {
      continue;
    }
    diag.Error(port.loc,
               std::format("checker formal '{}' is not singular, so it may "
                           "take no default or initial value",
                           port.name),
               Subclause("17.2"));
  }
}

void ValidateCheckerInterfaceFormals(const ModuleDecl* decl,
                                     const CompilationUnit* unit,
                                     const TypeShapeTables& types,
                                     DiagEngine& diag) {
  if (decl->decl_kind != ModuleDeclKind::kChecker) return;
  for (const PortDecl& port : decl->ports) {
    const std::string_view kName = port.data_type.type_name;
    if (!port.is_interface_port || types.typedefs.count(kName) != 0 ||
        types.class_names.count(kName) != 0) {
      continue;
    }
    const bool kNamesInterface = std::ranges::any_of(
        unit->interfaces,
        [kName](const ModuleDecl* ifc) { return ifc->name == kName; });
    if (!kNamesInterface) continue;
    diag.Error(port.loc,
               std::format("checker formal '{}' names interface '{}'; its "
                           "type shall be one a property formal can take",
                           port.name, kName),
               Subclause("17.2"));
  }
}

}  // namespace delta
