// §25.9: what the interface a virtual interface type names has to be: an
// interface, declaring the modport the type selects, and referring to no object
// outside its body.

#include "elaborator/virtual_interface_target.h"

#include <format>
#include <functional>
#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/interface_body_references.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// §25.9: leftmost identifier of a (possibly hierarchical) reference, e.g.
// "top" for the path top.u.sig.
std::string_view ReferenceRootName(const Expr* e) {
  while (e != nullptr) {
    if (e->kind == ExprKind::kIdentifier) return e->text;
    if (e->lhs != nullptr) {
      e = e->lhs;
    } else if (e->base != nullptr) {
      e = e->base;
    } else {
      break;
    }
  }
  return {};
}

// §25.9: a reference is "external" to an interface when it is a hierarchical
// (dotted or scope-qualified) reference whose root name is not declared
// within the interface body.
// §25.9: the node itself (ignoring children) is an external hierarchical
// reference — either a member access whose root is not local, or a
// scope-qualified identifier that is not local.
bool NodeIsExternalReference(
    const Expr* e, const std::unordered_set<std::string_view>& local) {
  if (e->kind == ExprKind::kMemberAccess) {
    auto root = ReferenceRootName(e);
    if (!root.empty() && local.find(root) == local.end()) return true;
  }
  if (e->kind == ExprKind::kIdentifier && !e->scope_prefix.empty() &&
      local.find(e->text) == local.end()) {
    return true;
  }
  return false;
}

bool ExprRefsOutsideInterface(
    const Expr* e, const std::unordered_set<std::string_view>& local);

// §25.9: recurse into the argument and element collections of a node.
bool ChildListRefsOutsideInterface(
    const Expr* e, const std::unordered_set<std::string_view>& local) {
  for (const auto* a : e->args)
    if (ExprRefsOutsideInterface(a, local)) return true;
  for (const auto* el : e->elements)
    if (ExprRefsOutsideInterface(el, local)) return true;
  return false;
}

bool ExprRefsOutsideInterface(
    const Expr* e, const std::unordered_set<std::string_view>& local) {
  if (e == nullptr) return false;
  if (NodeIsExternalReference(e, local)) return true;
  if (ExprRefsOutsideInterface(e->lhs, local)) return true;
  if (ExprRefsOutsideInterface(e->rhs, local)) return true;
  if (ExprRefsOutsideInterface(e->base, local)) return true;
  if (ExprRefsOutsideInterface(e->index, local)) return true;
  if (ExprRefsOutsideInterface(e->index_end, local)) return true;
  if (ExprRefsOutsideInterface(e->condition, local)) return true;
  if (ExprRefsOutsideInterface(e->true_expr, local)) return true;
  if (ExprRefsOutsideInterface(e->false_expr, local)) return true;
  if (ExprRefsOutsideInterface(e->repeat_count, local)) return true;
  if (ChildListRefsOutsideInterface(e, local)) return true;
  return false;
}

// §25.9: collect the port, parameter and modport names of an interface body.
void CollectInterfaceHeaderNames(const ModuleDecl* iface,
                                 std::unordered_set<std::string_view>& local) {
  for (const auto& p : iface->ports)
    if (!p.name.empty()) local.insert(p.name);
  for (const auto& param : iface->params)
    if (!param.first.empty()) local.insert(param.first);
  for (const auto* mp : iface->modports)
    if (mp && !mp->name.empty()) local.insert(mp->name);
}

// §25.9: collect the declared names and instance names of an interface's items.
void CollectInterfaceItemNames(const ModuleDecl* iface,
                               std::unordered_set<std::string_view>& local) {
  for (const auto* it : iface->items) {
    if (it == nullptr) continue;
    if (!it->name.empty()) local.insert(it->name);
    if (!it->inst_name.empty()) local.insert(it->inst_name);
  }
}

// §25.9: collect the names declared within an interface body (ports,
// parameters, modports, items and instance names) that count as "local".
std::unordered_set<std::string_view> CollectInterfaceLocalNames(
    const ModuleDecl* iface) {
  std::unordered_set<std::string_view> local;
  CollectInterfaceHeaderNames(iface, local);
  CollectInterfaceItemNames(iface, local);
  return local;
}

bool InterfaceContainsExternalReference(const ModuleDecl* iface) {
  // §25.9: a port that references another interface also disqualifies the
  // interface from being used as a virtual interface type.
  for (const auto& p : iface->ports) {
    if (p.is_interface_port) return true;
  }
  std::unordered_set<std::string_view> local =
      CollectInterfaceLocalNames(iface);
  for (const auto* it : iface->items) {
    if (it == nullptr) continue;
    if (ExprRefsOutsideInterface(it->init_expr, local)) return true;
    if (ExprRefsOutsideInterface(it->assign_lhs, local)) return true;
    if (ExprRefsOutsideInterface(it->assign_rhs, local)) return true;
  }
  return BodyRefersOutsideInterface(iface, local);
}

// §25.9: validate that a virtual interface declaration at `loc` names a real
// interface, a modport that exists on it, and an interface free of external
// references; `iface_decl` is the declaration its name finds, null for none.
void ValidateVirtualInterfaceTarget(SourceLoc loc, const ModuleDecl* iface_decl,
                                    std::string_view iface_name,
                                    std::string_view modport_name,
                                    DiagEngine& diag) {
  if (!iface_decl || iface_decl->decl_kind != ModuleDeclKind::kInterface) {
    diag.Error(loc,
               std::format("unknown interface '{}' in virtual interface "
                           "declaration",
                           iface_name),
               Subclause("25.9"));
  } else if (!modport_name.empty()) {
    bool found = false;
    for (const auto* mp : iface_decl->modports) {
      if (mp && mp->name == modport_name) {
        found = true;
        break;
      }
    }
    if (!found) {
      diag.Error(loc,
                 std::format("modport '{}' not found in interface '{}'",
                             modport_name, iface_name),
                 Subclause("25.9"));
    }
  }
  // §25.9: an interface containing hierarchical references to objects outside
  // its body (or ports that reference other interfaces) shall not be used as
  // the type of a virtual interface.
  if (iface_decl && iface_decl->decl_kind == ModuleDeclKind::kInterface &&
      InterfaceContainsExternalReference(iface_decl)) {
    diag.Error(loc,
               std::format("interface '{}' contains references to objects "
                           "outside its body and cannot be used as a "
                           "virtual interface",
                           iface_name),
               Subclause("25.9"));
  }
}

}  // namespace

void ValidateVirtualInterfaceType(
    const DataType& type, SourceLoc loc,
    const std::function<const ModuleDecl*(std::string_view)>& find_module,
    DiagEngine& diag) {
  if (type.kind != DataTypeKind::kVirtualInterface) return;
  ValidateVirtualInterfaceTarget(loc, find_module(type.type_name),
                                 type.type_name, type.modport_name, diag);
}

}  // namespace delta
