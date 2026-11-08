#include <algorithm>
#include <cstddef>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/std_package.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_site_lookup.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

using StdHandles = std::unordered_map<std::string_view, StdPackageMember>;

struct StdCallScope {
  const CompilationUnit& unit;
  TypeSite site;
  const TypedefMap& typedefs;
  StdHandles handles;
  std::unordered_set<std::string_view> aggregates;
};

std::optional<StdPackageMember> StdClassOfType(const DataType& type,
                                               const StdCallScope& scope) {
  if (type.kind != DataTypeKind::kNamed) return std::nullopt;
  const std::optional<StdPackageMember> kMember =
      StdPackageMemberNamed(type.type_name);
  if (!kMember || StdClassPrototype(*kMember).empty()) return std::nullopt;
  if (ClassIn(scope.unit, scope.site, type.type_name) != nullptr) {
    return std::nullopt;
  }
  return kMember;
}

void RecordDeclared(std::string_view name, const DataType& type,
                    const std::vector<Expr*>& dims, StdCallScope& scope) {
  if (!dims.empty() || IsAggregateType(type, scope.typedefs)) {
    scope.aggregates.insert(name);
    return;
  }
  const std::optional<StdPackageMember> kMember = StdClassOfType(type, scope);
  if (kMember) scope.handles[name] = *kMember;
}

void CollectStdHandlesInStmt(const Stmt* s, StdCallScope& scope) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl) {
    RecordDeclared(s->var_name, s->var_decl_type, s->var_unpacked_dims, scope);
  }
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CollectStdHandlesInStmt(sub, scope); });
}

bool CheckStdActualCount(const Expr* call, const StdMethodPrototype& method,
                         std::string_view what, std::string_view subclause,
                         DiagEngine& diag) {
  const std::size_t kGiven = call->args.size();
  const std::size_t kLeast = LeastActualsOf(method);
  const std::size_t kMost = MostActualsOf(method);
  if (kGiven <= kMost && kGiven >= kLeast) return true;
  const bool kTooMany = kGiven > kMost;
  const std::size_t kBound = kTooMany ? kMost : kLeast;
  diag.Error(call->range.start,
             std::format("{} takes at {} {} argument{}; {} given", what,
                         kTooMany ? "most" : "least", kBound,
                         kBound == 1 ? "" : "s", kGiven),
             Subclause(subclause));
  return false;
}

struct ClassBuiltinMethod {
  StdMethodPrototype prototype;
  std::string_view subclause;
};

const ClassBuiltinMethod* ClassBuiltinMethodNamed(std::string_view name) {
  static const std::vector<ClassBuiltinMethod> kMethods{
      {{"randomize", StdMethodKind::kFunction, "int", {}, false, true},
       "18.6.1"},
      {{"pre_randomize", StdMethodKind::kFunction, "void", {}}, "18.6.2"},
      {{"post_randomize", StdMethodKind::kFunction, "void", {}}, "18.6.2"},
      {{"rand_mode", StdMethodKind::kFunction, "void", {{"bit", "on_off"}}},
       "18.8"},
      {{"constraint_mode",
        StdMethodKind::kFunction,
        "void",
        {{"bit", "on_off"}}},
       "18.9"},
      {{"srandom", StdMethodKind::kFunction, "void", {{"int", "seed"}}},
       "18.13.3"},
      {{"get_randstate", StdMethodKind::kFunction, "string", {}}, "18.13.4"},
      {{"set_randstate",
        StdMethodKind::kFunction,
        "void",
        {{"string", "state"}}},
       "18.13.5"},
  };
  const auto kFound = std::ranges::find(
      kMethods, name,
      [](const ClassBuiltinMethod& m) { return m.prototype.name; });
  return kFound == kMethods.end() ? nullptr : &*kFound;
}

void CheckStdConstruction(const Expr* init, StdPackageMember member,
                          DiagEngine& diag) {
  if (!init || init->kind != ExprKind::kCall || init->text != "new") return;
  const StdMethodPrototype* constructor = StdMethodNamed(member, "new");
  if (constructor == nullptr) return;
  CheckStdActualCount(
      init, *constructor,
      std::format("constructor of class '{}'", StdPackageMemberName(member)),
      PrototypeSubclauseOfStdPackageMember(member), diag);
}

std::string_view MailboxMessageSubclause(std::string_view method) {
  if (method == "put") return "15.4.3";
  if (method == "try_put") return "15.4.4";
  if (method == "get") return "15.4.5";
  if (method == "try_get") return "15.4.6";
  if (method == "peek") return "15.4.7";
  return "15.4.8";
}

bool IsLeftHandExpr(const Expr* e) {
  if (e->kind == ExprKind::kConcatenation) {
    return std::ranges::all_of(e->elements, IsLeftHandExpr);
  }
  return e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kSelect ||
         e->kind == ExprKind::kMemberAccess;
}

void CheckMailboxMessage(const Expr* message, const StdMethodPrototype& method,
                         const StdCallScope& scope, DiagEngine& diag) {
  const std::string_view kSubclause = MailboxMessageSubclause(method.name);
  if (method.formals[0].by_reference && !IsLeftHandExpr(message)) {
    diag.Error(message->range.start,
               std::format("message of mailbox method '{}' is not a valid "
                           "left-hand expression",
                           method.name),
               Subclause(kSubclause));
  }
  if (message->kind == ExprKind::kIdentifier &&
      scope.aggregates.contains(message->text)) {
    diag.Error(message->range.start,
               std::format("message of mailbox method '{}' is of an unpacked "
                           "aggregate type; a mailbox message is singular",
                           method.name),
               Subclause(kSubclause));
  }
}

void CheckStdMethodOf(const Expr* access, const Expr* e,
                      const StdCallScope& scope, DiagEngine& diag) {
  if (!access || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution || !access->lhs ||
      access->lhs->kind != ExprKind::kIdentifier || !access->rhs) {
    return;
  }
  const auto kFound = scope.handles.find(access->lhs->text);
  if (kFound == scope.handles.end()) return;
  const StdPackageMember kMember = kFound->second;
  const std::string_view kClass = StdPackageMemberName(kMember);
  const std::string_view kMethod = access->rhs->text;
  const std::string_view kSubclause =
      PrototypeSubclauseOfStdPackageMember(kMember);
  const std::string kWhat =
      std::format("method '{}' of class '{}'", kMethod, kClass);
  const StdMethodPrototype* method = StdMethodNamed(kMember, kMethod);
  if (method == nullptr) {
    const ClassBuiltinMethod* builtin = ClassBuiltinMethodNamed(kMethod);
    if (builtin == nullptr) {
      diag.Error(
          e->range.start,
          std::format("class '{}' declares no method '{}'", kClass, kMethod),
          Subclause(kSubclause));
    } else if (!builtin->prototype.variadic) {
      CheckStdActualCount(e, builtin->prototype, kWhat, builtin->subclause,
                          diag);
    }
    return;
  }
  if (!CheckStdActualCount(e, *method, kWhat, kSubclause, diag)) return;
  if (kMember == StdPackageMember::kMailbox && !method->formals.empty()) {
    CheckMailboxMessage(e->args[0], *method, scope, diag);
  }
}

void CheckStdMethodCall(const Expr* e, const StdCallScope& scope,
                        DiagEngine& diag) {
  if (e->kind == ExprKind::kCall) CheckStdMethodOf(e->lhs, e, scope, diag);
}

void CheckStdCallsInExpr(const Expr* e, const StdCallScope& scope,
                         DiagEngine& diag) {
  if (!e) return;
  CheckStdMethodCall(e, scope, diag);
  ForEachExprChild(
      e, [&](const Expr* child) { CheckStdCallsInExpr(child, scope, diag); });
}

void CheckStdConstructionsInStmt(const Stmt* s, const StdCallScope& scope,
                                 DiagEngine& diag) {
  if (s->kind == StmtKind::kVarDecl) {
    const std::optional<StdPackageMember> kMember =
        StdClassOfType(s->var_decl_type, scope);
    if (kMember) CheckStdConstruction(s->var_init, *kMember, diag);
    return;
  }
  if (!s->lhs || s->lhs->kind != ExprKind::kIdentifier) return;
  const auto kFound = scope.handles.find(s->lhs->text);
  if (kFound != scope.handles.end()) {
    CheckStdConstruction(s->rhs, kFound->second, diag);
  }
}

void CheckStdCallsInStmt(const Stmt* s, const StdCallScope& scope,
                         DiagEngine& diag) {
  if (!s) return;
  CheckStdConstructionsInStmt(s, scope, diag);
  if (s->kind == StmtKind::kExprStmt) {
    CheckStdMethodOf(s->expr, s->expr, scope, diag);
  }
  ForEachChildExpr(
      s, [&](Expr* const& e) { CheckStdCallsInExpr(e, scope, diag); });
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckStdCallsInStmt(sub, scope, diag); });
}

template <typename Visit>
void ForEachBodyStmt(const ModuleDecl* decl, Visit visit) {
  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      visit(item->body);
    } else if (item->kind == ModuleItemKind::kFunctionDecl ||
               item->kind == ModuleItemKind::kTaskDecl) {
      for (const auto* s : item->func_body_stmts) visit(s);
    }
  }
}

void CollectStdHandlesInItems(const ModuleDecl* decl, StdCallScope& scope,
                              DiagEngine& diag) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    RecordDeclared(item->name, item->data_type, item->unpacked_dims, scope);
    const auto kFound = scope.handles.find(item->name);
    if (kFound != scope.handles.end()) {
      CheckStdConstruction(item->init_expr, kFound->second, diag);
    }
  }
}

}  // namespace

void Elaborator::ValidateStdClassMethodCalls(const ModuleDecl* decl) {
  StdCallScope scope{
      *unit_,
      TypeSite{&decl->items, decl->items.size(), SiteKind::kModule},
      typedefs_,
      {},
      {}};
  CollectStdHandlesInItems(decl, scope, diag_);
  ForEachBodyStmt(
      decl, [&scope](const Stmt* s) { CollectStdHandlesInStmt(s, scope); });
  if (scope.handles.empty()) return;
  ForEachBodyStmt(decl, [&scope, this](const Stmt* s) {
    CheckStdCallsInStmt(s, scope, diag_);
  });
}

}  // namespace delta
