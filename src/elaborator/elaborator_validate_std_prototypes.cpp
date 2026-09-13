#include <cstddef>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/std_package.h"
#include "parser/ast.h"

namespace delta {

namespace {

// The handles of std classes in scope, by name: the member each is a handle
// of. Only the classes whose prototype src/elaborator/std_package.h writes
// down are collected, since a call on any other cannot be checked against
// one.
using StdHandles = std::unordered_map<std::string_view, StdPackageMember>;

// The std class a declared type names, where it names one with a prototype.
std::optional<StdPackageMember> StdClassOfType(const DataType& type) {
  if (type.kind != DataTypeKind::kNamed) return std::nullopt;
  const std::optional<StdPackageMember> kMember =
      StdPackageMemberNamed(type.type_name);
  if (!kMember || StdClassPrototype(*kMember).empty()) return std::nullopt;
  return kMember;
}

// Collects the handles a statement and those under it declare.
void CollectStdHandlesInStmt(const Stmt* s, StdHandles& handles) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl) {
    const std::optional<StdPackageMember> kMember =
        StdClassOfType(s->var_decl_type);
    if (kMember) handles[s->var_name] = *kMember;
  }
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CollectStdHandlesInStmt(sub, handles); });
}

// §G.3: a call obj.method(...) on a handle of a std class is checked against
// the class's prototype -- the method shall be one the prototype declares,
// and the actuals shall be no fewer than its formals without a default and no
// more than its formals. The subclause cited is the one giving the prototype.
void CheckStdMethodCall(const Expr* e, const StdHandles& handles,
                        DiagEngine& diag) {
  if (e->kind != ExprKind::kCall || !e->lhs ||
      e->lhs->kind != ExprKind::kMemberAccess || e->lhs->is_scope_resolution ||
      !e->lhs->lhs || e->lhs->lhs->kind != ExprKind::kIdentifier ||
      !e->lhs->rhs) {
    return;
  }
  const auto kFound = handles.find(e->lhs->lhs->text);
  if (kFound == handles.end()) return;
  const StdPackageMember kMember = kFound->second;
  const std::string_view kClass = StdPackageMemberName(kMember);
  const std::string_view kMethod = e->lhs->rhs->text;
  const std::string_view kSubclause =
      PrototypeSubclauseOfStdPackageMember(kMember);
  const StdMethodPrototype* method = StdMethodNamed(kMember, kMethod);
  if (method == nullptr) {
    diag.Error(
        e->range.start,
        std::format("class '{}' declares no method '{}'", kClass, kMethod),
        Subclause(kSubclause));
    return;
  }
  const std::size_t kGiven = e->args.size();
  const std::size_t kLeast = LeastActualsOf(*method);
  const std::size_t kMost = MostActualsOf(*method);
  if (kGiven > kMost) {
    diag.Error(
        e->range.start,
        std::format("method '{}' of class '{}' takes at most {} "
                    "argument{}; {} given",
                    kMethod, kClass, kMost, kMost == 1 ? "" : "s", kGiven),
        Subclause(kSubclause));
  } else if (kGiven < kLeast) {
    diag.Error(
        e->range.start,
        std::format("method '{}' of class '{}' takes at least {} "
                    "argument{}; {} given",
                    kMethod, kClass, kLeast, kLeast == 1 ? "" : "s", kGiven),
        Subclause(kSubclause));
  }
}

void CheckStdCallsInExpr(const Expr* e, const StdHandles& handles,
                         DiagEngine& diag) {
  if (!e) return;
  CheckStdMethodCall(e, handles, diag);
  ForEachExprChild(
      e, [&](const Expr* child) { CheckStdCallsInExpr(child, handles, diag); });
}

// The prototype puts no condition on where the call stands, so every
// position a statement holds an expression or a statement in is visited;
// ForEachChildExpr and ForEachChildStmt in elaborator_validate_internal.h
// state those positions once for the whole elaborator.
void CheckStdCallsInStmt(const Stmt* s, const StdHandles& handles,
                         DiagEngine& diag) {
  if (!s) return;
  ForEachChildExpr(
      s, [&](Expr* const& e) { CheckStdCallsInExpr(e, handles, diag); });
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckStdCallsInStmt(sub, handles, diag); });
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

// The module-scope variables of a std class with a prototype.
void CollectStdHandlesInItems(const ModuleDecl* decl, StdHandles& handles) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    const std::optional<StdPackageMember> kMember =
        StdClassOfType(item->data_type);
    if (kMember) handles[item->name] = *kMember;
  }
}

}  // namespace

void Elaborator::ValidateStdClassMethodCalls(const ModuleDecl* decl) {
  // The handles: the module-scope variables of a std class, and those the
  // procedural bodies and subroutines declare.
  StdHandles handles;
  CollectStdHandlesInItems(decl, handles);
  ForEachBodyStmt(
      decl, [&handles](const Stmt* s) { CollectStdHandlesInStmt(s, handles); });
  if (handles.empty()) return;
  ForEachBodyStmt(decl, [&handles, this](const Stmt* s) {
    CheckStdCallsInStmt(s, handles, diag_);
  });
}

}  // namespace delta
