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

// The handles of std classes in scope, by name: the member each is a handle
// of. Only the classes whose prototype src/elaborator/std_package.h writes
// down are collected, since a call on any other cannot be checked against
// one.
using StdHandles = std::unordered_map<std::string_view, StdPackageMember>;

// What the checks know of one module: where its type names are looked up,
// the handles of std classes it declares, and the variables it declares of an
// unpacked aggregate type (§6.4), which no mailbox message is.
struct StdCallScope {
  const CompilationUnit& unit;
  TypeSite site;
  const TypedefMap& typedefs;
  StdHandles handles;
  std::unordered_set<std::string_view> aggregates;
};

// The std class a declared type names, where it names one with a prototype.
// §15.2: user code may declare a class under a std class's name, and a type
// naming a class the module or the compilation unit declares is that class.
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

// Records the declaration of `name`, of `type` with the unpacked dimensions
// `dims`: a variable of an unpacked aggregate type, or a handle of a std
// class. §7.4 with §7.8 and §7.10: a declaration with an unpacked dimension
// is an array, a queue or an associative array, not a handle, and
// `q.push_back(t)` calls the container's method (§7.10.2).
void RecordDeclared(std::string_view name, const DataType& type,
                    const std::vector<Expr*>& dims, StdCallScope& scope) {
  if (!dims.empty() || IsAggregateType(type, scope.typedefs)) {
    scope.aggregates.insert(name);
    return;
  }
  const std::optional<StdPackageMember> kMember = StdClassOfType(type, scope);
  if (kMember) scope.handles[name] = *kMember;
}

// Collects the declarations a statement and those under it make.
void CollectStdHandlesInStmt(const Stmt* s, StdCallScope& scope) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl) {
    RecordDeclared(s->var_name, s->var_decl_type, s->var_unpacked_dims, scope);
  }
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CollectStdHandlesInStmt(sub, scope); });
}

// The count of actuals a call passes against what a method takes, reported
// under `subclause` as a call of `what` -- "method 'get' of class 'mailbox'"
// or "constructor of class 'semaphore'". Answers whether the count is one the
// method takes.
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

// §18.6.1, §18.6.2, §18.8, §18.9 and §18.13.3 to §18.13.5: the built-in
// methods every class has without declaring them, as a call on a handle of
// the object takes them, each with the subclause giving it. randomize takes
// any number of actuals, and rand_mode and constraint_mode, naming no
// variable or constraint, take the one on/off actual of their void form.
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

// §G.3 through §G.7: a construction new(...) of a handle of a std class
// passes the actuals the prototype's constructor takes; a class without one
// is the concern of the rule that refuses its construction outright.
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

// §15.4.3 through §15.4.8: the subclause giving the mailbox method `method`,
// one of the six whose one formal is the message.
std::string_view MailboxMessageSubclause(std::string_view method) {
  if (method == "put") return "15.4.3";
  if (method == "try_put") return "15.4.4";
  if (method == "get") return "15.4.5";
  if (method == "try_get") return "15.4.6";
  if (method == "peek") return "15.4.7";
  return "15.4.8";
}

// Whether `e` is a valid left-hand expression: a variable named by an
// identifier or a member, a select of one, or a concatenation of them.
bool IsLeftHandExpr(const Expr* e) {
  if (e->kind == ExprKind::kConcatenation) {
    return std::ranges::all_of(e->elements, IsLeftHandExpr);
  }
  return e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kSelect ||
         e->kind == ExprKind::kMemberAccess;
}

// §15.4.3 through §15.4.8: a mailbox message is a singular expression, and
// the message get(), try_get(), peek() and try_peek() store into, passed by
// reference, is a valid left-hand expression.
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

// §G.3: a call obj.method(...) on a handle of a std class is checked against
// the class's prototype -- the method shall be one the prototype declares or
// one every class has built in, and the actuals shall be no fewer than its
// formals without a default and no more than its formals. The subclause cited
// is the one giving the prototype, or the method where it is built in.
void CheckStdMethodCall(const Expr* e, const StdCallScope& scope,
                        DiagEngine& diag) {
  if (e->kind != ExprKind::kCall || !e->lhs ||
      e->lhs->kind != ExprKind::kMemberAccess || e->lhs->is_scope_resolution ||
      !e->lhs->lhs || e->lhs->lhs->kind != ExprKind::kIdentifier ||
      !e->lhs->rhs) {
    return;
  }
  const auto kFound = scope.handles.find(e->lhs->lhs->text);
  if (kFound == scope.handles.end()) return;
  const StdPackageMember kMember = kFound->second;
  const std::string_view kClass = StdPackageMemberName(kMember);
  const std::string_view kMethod = e->lhs->rhs->text;
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

void CheckStdCallsInExpr(const Expr* e, const StdCallScope& scope,
                         DiagEngine& diag) {
  if (!e) return;
  CheckStdMethodCall(e, scope, diag);
  ForEachExprChild(
      e, [&](const Expr* child) { CheckStdCallsInExpr(child, scope, diag); });
}

// The prototype puts no condition on where the call stands, so every
// position a statement holds an expression or a statement in is visited;
// ForEachChildExpr and ForEachChildStmt in elaborator_validate_internal.h
// state those positions once for the whole elaborator.
// The constructions a statement holds: a declaration of a std handle
// initialized with new, and an assignment of new to one.
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
  ForEachChildExpr(
      s, [&](Expr* const& e) { CheckStdCallsInExpr(e, scope, diag); });
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckStdCallsInStmt(sub, scope, diag); });
}

// The statements a module's procedural blocks and subroutines hold: each
// procedural item's body and each function's or task's body statements.
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

// The module-scope variables, and the construction each handle of a std class
// with a prototype is declared with, if any.
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
  // The declarations: the module-scope variables, and those the procedural
  // bodies and subroutines declare.
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
