// §25.7: the subroutines a modport imports, held to the interface's
// declarations of them and to the calls made through them.

#include "elaborator/elaborator_modport_imports.h"

#include <cstddef>
#include <format>
#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

bool PrototypeMatchesSubroutine(const ModuleItem* proto,
                                const ModuleItem* body) {
  if (proto->kind != body->kind) return false;
  if (proto->func_args.size() != body->func_args.size()) return false;
  for (size_t i = 0; i < proto->func_args.size(); ++i) {
    const DataType& pa = proto->func_args[i].data_type;
    const DataType& ba = body->func_args[i].data_type;
    if (!TypesMatch(pa, ba)) return false;
    // §25.7 requires an exact match: TypesMatch does not tell apart packed
    // bounds that fold only in a scope, so widths are compared too, which
    // rejects arguments such as logic [7:0] against logic [3:0] however their
    // bounds are written.
    if (EvalTypeWidth(pa) != EvalTypeWidth(ba)) return false;
    if (proto->func_args[i].direction != body->func_args[i].direction)
      return false;
  }
  // A modport function prototype keeps its return type in `data_type`, while a
  // subroutine's body keeps it in `return_type`; compare the matching fields.
  return proto->kind != ModuleItemKind::kFunctionDecl ||
         TypesMatch(proto->data_type, body->return_type);
}

namespace {

// The task or function `name` the interface `iface` defines among its own
// items; null where it defines none, an `extern` prototype of one defined in a
// module (§25.7.4) not being a definition.
const ModuleItem* InterfaceSubroutine(const ModuleDecl* iface,
                                      std::string_view name) {
  for (const ModuleItem* item : iface->items) {
    bool subroutine = item->kind == ModuleItemKind::kTaskDecl ||
                      item->kind == ModuleItemKind::kFunctionDecl;
    if (subroutine && !item->is_extern && item->name == name) return item;
  }
  return nullptr;
}

// §25.7: a formal name the prototype `proto` gives is the name the declaration
// `decl`, of as many arguments, gives the formal in its place.
bool FormalNamesAgree(const ModuleItem* proto, const ModuleItem* decl) {
  for (size_t i = 0; i < proto->func_args.size(); ++i) {
    std::string_view name = proto->func_args[i].name;
    if (!name.empty() && name != decl->func_args[i].name) return false;
  }
  return true;
}

// The subroutine `name` the modport `mp` imports, null where it imports none.
const ModportPort* ModportImport(const ModportDecl* mp, std::string_view name) {
  for (const ModportPort& port : mp->ports) {
    if (port.is_import && port.name == name) return &port;
  }
  return nullptr;
}

// The slot of the call `call` holding the actual of the formal at `index`,
// named `name`: its place among the ordered actuals, or the named actual of
// that name; null where the call writes neither. `ordered` is how many of the
// call's actuals are ordered ones, which come before every named one.
Expr** ActualSlot(Expr* call, size_t ordered, size_t index,
                  std::string_view name) {
  if (index < ordered) return &call->args[index];
  for (size_t k = 0; k < call->arg_names.size(); ++k) {
    if (call->arg_names[k] == name) return &call->args[ordered + k];
  }
  return nullptr;
}

// §25.7: a call through the full prototype `proto` the modport `mp` imports.
// Each formal the call leaves without an actual takes the default the
// prototype gives it, which is written into the call in the formal's place;
// one the prototype gives no default is reported.
void FillPrototypeDefaults(Expr* call, const ModuleItem* proto,
                           const ModportDecl* mp, DiagEngine& diag) {
  size_t ordered = call->args.size() - call->arg_names.size();
  for (size_t j = 0; j < proto->func_args.size(); ++j) {
    const FunctionArg& formal = proto->func_args[j];
    Expr** slot = ActualSlot(call, ordered, j, formal.name);
    if (slot != nullptr && *slot != nullptr) continue;
    if (formal.default_value == nullptr) {
      diag.Error(call->range.start,
                 std::format("the call of '{}' through modport '{}' omits "
                             "argument '{}', which the modport's prototype "
                             "gives no default",
                             proto->name, mp->name, formal.name),
                 Subclause("25.7"));
      continue;
    }
    if (slot != nullptr) {
      *slot = formal.default_value;
    } else if (call->arg_names.empty()) {
      call->args.push_back(formal.default_value);
    } else {
      call->arg_names.push_back(formal.name);
      call->args.push_back(formal.default_value);
    }
  }
}

// §25.7: a call through an import by the identifier alone of the interface's
// own subroutine `decl`, which binds no actual by name and leaves no formal to
// its default, since either needs a full prototype in the modport `mp`.
void CheckIdentifierImportCall(const Expr* call, const ModuleItem* decl,
                               const ModportDecl* mp, DiagEngine& diag) {
  std::string_view need;
  if (!call->arg_names.empty()) {
    need = "binds an argument by name";
  } else {
    for (size_t j = 0; j < decl->func_args.size(); ++j) {
      if (j < call->args.size() && call->args[j] != nullptr) continue;
      need = "relies on a default argument value";
      break;
    }
  }
  if (need.empty()) return;
  diag.Error(call->range.start,
             std::format("the call of '{}' through modport '{}' {}, which "
                         "needs a full prototype of '{}' in the modport",
                         decl->name, mp->name, need, decl->name),
             Subclause("25.7"));
}

// The call `call`, where it is made through a port `ports` names of a
// subroutine the port's modport imports.
void CheckCallThroughModport(Expr* call, const SelectedModports& ports,
                             DiagEngine& diag) {
  const Expr* callee = call->lhs;
  if (callee == nullptr || callee->kind != ExprKind::kMemberAccess) return;
  auto it = ports.find(callee->lhs->text);
  if (it == ports.end()) return;
  const ModportDecl* mp = it->second.modport;
  const ModportPort* imported = ModportImport(mp, callee->rhs->text);
  if (imported == nullptr) return;
  if (imported->prototype != nullptr) {
    FillPrototypeDefaults(call, imported->prototype, mp, diag);
    return;
  }
  // An identifier-only import of a subroutine the interface does not define
  // is reported once, at the modport (CheckModportImport).
  const ModuleItem* decl =
      InterfaceSubroutine(it->second.iface, imported->name);
  if (decl != nullptr) CheckIdentifierImportCall(call, decl, mp, diag);
}

void CheckCallsInExpr(Expr* e, const SelectedModports& ports,
                      DiagEngine& diag) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kCall) CheckCallThroughModport(e, ports, diag);
  CheckCallsInExpr(e->lhs, ports, diag);
  CheckCallsInExpr(e->rhs, ports, diag);
  CheckCallsInExpr(e->base, ports, diag);
  CheckCallsInExpr(e->index, ports, diag);
  CheckCallsInExpr(e->condition, ports, diag);
  CheckCallsInExpr(e->true_expr, ports, diag);
  CheckCallsInExpr(e->false_expr, ports, diag);
  for (Expr* element : e->elements) CheckCallsInExpr(element, ports, diag);
  for (Expr* arg : e->args) CheckCallsInExpr(arg, ports, diag);
}

void CheckCallsInStmt(const Stmt* s, const SelectedModports& ports,
                      DiagEngine& diag) {
  if (s == nullptr) return;
  CheckCallsInExpr(s->lhs, ports, diag);
  CheckCallsInExpr(s->rhs, ports, diag);
  CheckCallsInExpr(s->expr, ports, diag);
  CheckCallsInExpr(s->condition, ports, diag);
  CheckCallsInExpr(s->var_init, ports, diag);
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckCallsInStmt(sub, ports, diag); });
}

}  // namespace

void CheckModportImport(const ModuleDecl* iface, const ModportDecl* mp,
                        const ModportPort& port, DiagEngine& diag) {
  if (!port.is_import) return;
  const ModuleItem* decl = InterfaceSubroutine(iface, port.name);
  if (port.prototype == nullptr) {
    if (decl != nullptr) return;
    diag.Error(mp->loc,
               std::format("modport '{}' imports '{}', which interface '{}' "
                           "does not define, by its name alone; importing a "
                           "subroutine another module defines needs a full "
                           "prototype",
                           mp->name, port.name, iface->name),
               Subclause("25.7"));
    return;
  }
  if (decl == nullptr || (PrototypeMatchesSubroutine(port.prototype, decl) &&
                          FormalNamesAgree(port.prototype, decl))) {
    return;
  }
  diag.Error(port.prototype->loc,
             std::format("the prototype of '{}' modport '{}' imports does not "
                         "match its declaration in interface '{}'",
                         port.name, mp->name, iface->name),
             Subclause("25.7"));
}

void CheckModportImportCalls(const ModuleDecl* decl,
                             const SelectedModports& ports, DiagEngine& diag) {
  if (ports.empty()) return;
  for (ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckCallsInExpr(item->assign_rhs, ports, diag);
    } else {
      CheckCallsInStmt(item->body, ports, diag);
    }
  }
}

}  // namespace delta
