// §15.4.9's compile-time check of a parameterized mailbox: the argument a
// send or receive method passes is type-equivalent to the mailbox's element
// type.

#include <format>
#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// §15.4.9: coarse category of a data type for the compile-time equivalence
// check a parameterized mailbox applies to its method arguments. A
// parameterized mailbox transfers exactly one element type, so an argument in a
// different category (integral vs. real vs. string) is a type mismatch the
// compiler must reject up front. Returns -1 for a type this check does not
// classify (e.g. a class handle, struct, or the special dynamic_type), which
// suppresses the diagnostic so a case whose equivalence cannot be decided this
// coarsely is left to run time rather than wrongly rejected.
int MailboxTypeCategory(DataTypeKind k) {
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
      return 0;  // integral
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
      return 1;  // real
    case DataTypeKind::kString:
      return 2;  // string
    default:
      return -1;  // not classified by this check
  }
}

// §15.4.9: the mailbox methods whose argument the compiler type-checks against
// the mailbox element type — the send methods carry a message value, the
// receive methods a reference destination; both must match the parameterized
// type.
bool IsMailboxTransferMethod(std::string_view m) {
  return m == "put" || m == "try_put" || m == "get" || m == "peek" ||
         m == "try_get" || m == "try_peek";
}

// §15.4.9: resolves the element-type kind of a parameterized mailbox
// declaration
// (`mailbox #(T)`, or a typedef of that form). Returns kImplicit when the
// declaration is not a parameterized mailbox with a concrete element type — an
// unparameterized (typeless) mailbox, or `mailbox #(dynamic_type)`, imposes no
// compile-time constraint and is left to the run-time check.
DataTypeKind MailboxElementKind(const DataType& dt,
                                const TypedefMap& typedefs) {
  const DataType* mbx = &dt;
  // Follow one level of typedef: `typedef mailbox #(T) name; name v;`.
  if (dt.kind == DataTypeKind::kNamed && dt.type_params.empty()) {
    auto it = typedefs.find(dt.type_name);
    if (it != typedefs.end()) mbx = &it->second;
  }
  if (mbx->kind != DataTypeKind::kNamed || mbx->type_name != "mailbox")
    return DataTypeKind::kImplicit;
  if (mbx->type_params.empty()) return DataTypeKind::kImplicit;
  return mbx->type_params[0].kind;
}

// §15.4.9: the data-type kind of a mailbox method argument. Literals carry
// their own type; an identifier is resolved through the module-scope variable
// kinds. Anything else (a computed expression) yields kImplicit and is not
// checked.
DataTypeKind MailboxArgKind(
    const Expr* a,
    const std::unordered_map<std::string_view, DataTypeKind>& var_kinds) {
  if (!a) return DataTypeKind::kImplicit;
  switch (a->kind) {
    case ExprKind::kStringLiteral:
      return DataTypeKind::kString;
    case ExprKind::kRealLiteral:
      return DataTypeKind::kReal;
    case ExprKind::kIntegerLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
      return DataTypeKind::kInt;
    case ExprKind::kIdentifier: {
      auto it = var_kinds.find(a->text);
      return it != var_kinds.end() ? it->second : DataTypeKind::kImplicit;
    }
    default:
      return DataTypeKind::kImplicit;
  }
}

// §15.4.9: recursively inspects `e` for a parameterized-mailbox method call
// `mbx.method(arg)` and rejects an argument whose type is not equivalent to the
// mailbox element type — the mismatch the compiler catches up front instead of
// at run time.
void CheckMailboxCallExpr(
    const Expr* e,
    const std::unordered_map<std::string_view, DataTypeKind>& mbx_elem,
    const std::unordered_map<std::string_view, DataTypeKind>& var_kinds,
    DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kCall && e->lhs &&
      e->lhs->kind == ExprKind::kMemberAccess && !e->lhs->is_scope_resolution &&
      e->lhs->lhs && e->lhs->lhs->kind == ExprKind::kIdentifier &&
      e->lhs->rhs) {
    std::string_view obj = e->lhs->lhs->text;
    std::string_view method = e->lhs->rhs->text;
    auto it = mbx_elem.find(obj);
    if (it != mbx_elem.end() && IsMailboxTransferMethod(method) &&
        !e->args.empty()) {
      int ec = MailboxTypeCategory(it->second);
      int ac = MailboxTypeCategory(MailboxArgKind(e->args[0], var_kinds));
      if (ec >= 0 && ac >= 0 && ec != ac) {
        diag.Error(e->range.start,
                   std::format("argument to mailbox method '{}' is not "
                               "type-equivalent to the element type of "
                               "parameterized mailbox '{}'",
                               method, obj),
                   Subclause("15.4.9"));
      }
    }
  }
  CheckMailboxCallExpr(e->lhs, mbx_elem, var_kinds, diag);
  CheckMailboxCallExpr(e->rhs, mbx_elem, var_kinds, diag);
  CheckMailboxCallExpr(e->condition, mbx_elem, var_kinds, diag);
  CheckMailboxCallExpr(e->true_expr, mbx_elem, var_kinds, diag);
  CheckMailboxCallExpr(e->false_expr, mbx_elem, var_kinds, diag);
  CheckMailboxCallExpr(e->base, mbx_elem, var_kinds, diag);
  CheckMailboxCallExpr(e->index, mbx_elem, var_kinds, diag);
  CheckMailboxCallExpr(e->index_end, mbx_elem, var_kinds, diag);
  for (auto* a : e->args) CheckMailboxCallExpr(a, mbx_elem, var_kinds, diag);
  for (auto* el : e->elements)
    CheckMailboxCallExpr(el, mbx_elem, var_kinds, diag);
}

// §15.4.9 puts no condition on where the parameterized-mailbox method call it
// type-checks stands, and A.6.4 makes a subroutine_call_statement a
// statement_item, so every position a statement holds a statement in is one the
// report is owed at. ForEachChildStmt in elaborator_validate_internal.h states
// those positions once for the whole elaborator, which is why the list is not
// written out again here.
void CheckMailboxCallStmt(
    const Stmt* s,
    const std::unordered_map<std::string_view, DataTypeKind>& mbx_elem,
    const std::unordered_map<std::string_view, DataTypeKind>& var_kinds,
    DiagEngine& diag) {
  if (!s) return;
  CheckMailboxCallExpr(s->expr, mbx_elem, var_kinds, diag);
  CheckMailboxCallExpr(s->lhs, mbx_elem, var_kinds, diag);
  CheckMailboxCallExpr(s->rhs, mbx_elem, var_kinds, diag);
  CheckMailboxCallExpr(s->condition, mbx_elem, var_kinds, diag);
  CheckMailboxCallExpr(s->for_cond, mbx_elem, var_kinds, diag);
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckMailboxCallStmt(sub, mbx_elem, var_kinds, diag);
  });
}

}  // namespace

void Elaborator::ValidateParameterizedMailboxCalls(const ModuleDecl* decl) {
  // Collect the parameterized-mailbox variables (name -> element kind) and the
  // kind of every module-scope variable, so an identifier argument can be
  // typed.
  std::unordered_map<std::string_view, DataTypeKind> mbx_elem;
  std::unordered_map<std::string_view, DataTypeKind> var_kinds;
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    var_kinds[item->name] = item->data_type.kind;
    DataTypeKind ek = MailboxElementKind(item->data_type, typedefs_);
    if (MailboxTypeCategory(ek) >= 0) mbx_elem[item->name] = ek;
  }
  if (mbx_elem.empty()) return;

  for (const auto* item : decl->items) {
    if (IsProceduralItemKind(item->kind)) {
      CheckMailboxCallStmt(item->body, mbx_elem, var_kinds, diag_);
    }
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      for (auto* s : item->func_body_stmts)
        CheckMailboxCallStmt(s, mbx_elem, var_kinds, diag_);
    }
  }
}

}  // namespace delta
