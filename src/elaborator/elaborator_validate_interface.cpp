#include <format>
#include <optional>
#include <unordered_map>
#include <unordered_set>
#include <utility>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

namespace {

using VifTypeMap = std::unordered_map<std::string_view, std::string_view>;
using VifModportMap = std::unordered_map<std::string_view, std::string_view>;

std::string_view ResolveVifInterfaceType(const DataType& dt,
                                         const TypedefMap& typedefs) {
  if (dt.kind == DataTypeKind::kVirtualInterface) return dt.type_name;
  if (dt.kind == DataTypeKind::kNamed) {
    auto it = typedefs.find(dt.type_name);
    if (it != typedefs.end() &&
        it->second.kind == DataTypeKind::kVirtualInterface) {
      return it->second.type_name;
    }
  }
  return {};
}

std::string_view ResolveVifModport(const DataType& dt,
                                   const TypedefMap& typedefs) {
  if (dt.kind == DataTypeKind::kVirtualInterface) return dt.modport_name;
  if (dt.kind == DataTypeKind::kNamed) {
    auto it = typedefs.find(dt.type_name);
    if (it != typedefs.end() &&
        it->second.kind == DataTypeKind::kVirtualInterface) {
      return it->second.modport_name;
    }
  }
  return {};
}

// Extends the module-level virtual-interface type/modport maps with the
// virtual-interface formal arguments of a task or function `item`, returning
// the scoped maps used while walking that subroutine's body.
std::pair<VifTypeMap, VifModportMap> BuildScopedVifMaps(
    const ModuleItem* item, const VifTypeMap& base_vifs,
    const VifModportMap& base_mps, const TypedefMap& typedefs) {
  VifTypeMap scoped = base_vifs;
  VifModportMap scoped_mps = base_mps;
  for (const auto& a : item->func_args) {
    auto t = ResolveVifInterfaceType(a.data_type, typedefs);
    if (!t.empty()) {
      scoped[a.name] = t;
      scoped_mps[a.name] = ResolveVifModport(a.data_type, typedefs);
    }
  }
  return {std::move(scoped), std::move(scoped_mps)};
}

const ModuleDecl* FindInterfaceDeclByName(const CompilationUnit* unit,
                                          std::string_view name) {
  if (!unit) return nullptr;
  for (const auto* i : unit->interfaces) {
    if (i && i->name == name) return i;
  }
  for (const auto* m : unit->modules) {
    if (m && m->name == name && m->decl_kind == ModuleDeclKind::kInterface) {
      return m;
    }
  }
  return nullptr;
}

// Diagnoses a virtual-interface clocking-block access of the form
// `vif.block.signal` for one resolved member-access expression `e`, where
// `vif_it` is the entry that resolved the base identifier to its interface
// type. Reports the same set of errors the inlined block did.
void CheckResolvedVifClockingAccess(const Expr* e,
                                    const VifTypeMap::const_iterator& vif_it,
                                    const VifModportMap& vif_mps,
                                    const CompilationUnit* unit,
                                    DiagEngine& diag) {
  std::string_view block_name;
  if (e->lhs->rhs && e->lhs->rhs->kind == ExprKind::kIdentifier) {
    block_name = e->lhs->rhs->text;
  } else if (!e->lhs->text.empty()) {
    block_name = e->lhs->text;
  }
  std::string_view sig_name;
  if (e->rhs && e->rhs->kind == ExprKind::kIdentifier) {
    sig_name = e->rhs->text;
  } else if (!e->text.empty()) {
    sig_name = e->text;
  }
  const auto* iface = FindInterfaceDeclByName(unit, vif_it->second);
  if (!iface || block_name.empty()) return;

  std::string_view modport_name;
  auto mp_it = vif_mps.find(e->lhs->lhs->text);
  if (mp_it != vif_mps.end()) modport_name = mp_it->second;

  const ModportDecl* modport = nullptr;
  if (!modport_name.empty()) {
    for (const auto* mp : iface->modports) {
      if (mp && mp->name == modport_name) {
        modport = mp;
        break;
      }
    }
  }

  const ModuleItem* cb_item = nullptr;
  bool member_exists = false;
  for (const auto* it : iface->items) {
    if (it->kind == ModuleItemKind::kClockingBlock && it->name == block_name) {
      cb_item = it;
      break;
    }
    if ((it->kind == ModuleItemKind::kVarDecl ||
         it->kind == ModuleItemKind::kNetDecl) &&
        it->name == block_name) {
      member_exists = true;
    }
  }

  if (cb_item && modport) {
    bool clocking_in_modport = false;
    for (const auto& p : modport->ports) {
      if (p.is_clocking && p.name == block_name) {
        clocking_in_modport = true;
        break;
      }
    }
    if (!clocking_in_modport) {
      diag.Error(
          e->range.start,
          std::format("clocking block '{}' is not accessible through modport "
                      "'{}' of interface '{}'",
                      block_name, modport_name, vif_it->second));
      cb_item = nullptr;
    }
  }

  if (!cb_item && !member_exists) {
    diag.Error(e->range.start,
               std::format("'{}' is not a clocking block or member of "
                           "interface '{}'",
                           block_name, vif_it->second));
  } else if (cb_item && !sig_name.empty()) {
    bool signal_found = false;
    for (const auto& sig : cb_item->clocking_signals) {
      if (sig.name == sig_name) {
        signal_found = true;
        break;
      }
    }
    if (!signal_found) {
      diag.Error(e->range.start,
                 std::format("'{}' is not a signal of clocking block '{}' in "
                             "interface '{}'",
                             sig_name, block_name, vif_it->second));
    }
  }
}

void CheckVifClockingExpr(const Expr* e, const VifTypeMap& vifs,
                          const VifModportMap& vif_mps,
                          const CompilationUnit* unit, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->lhs &&
      e->lhs->kind == ExprKind::kMemberAccess && e->lhs->lhs &&
      e->lhs->lhs->kind == ExprKind::kIdentifier) {
    auto vif_it = vifs.find(e->lhs->lhs->text);
    if (vif_it != vifs.end()) {
      CheckResolvedVifClockingAccess(e, vif_it, vif_mps, unit, diag);
    }
  }
  CheckVifClockingExpr(e->lhs, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(e->rhs, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(e->base, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(e->index, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(e->condition, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(e->true_expr, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(e->false_expr, vifs, vif_mps, unit, diag);
  for (const auto* elem : e->elements) {
    CheckVifClockingExpr(elem, vifs, vif_mps, unit, diag);
  }
  for (const auto* arg : e->args) {
    CheckVifClockingExpr(arg, vifs, vif_mps, unit, diag);
  }
}

void WalkStmtsForVifClocking(const Stmt* s, const VifTypeMap& vifs,
                             const VifModportMap& vif_mps,
                             const CompilationUnit* unit, DiagEngine& diag) {
  if (!s) return;
  CheckVifClockingExpr(s->lhs, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(s->rhs, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(s->expr, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(s->condition, vifs, vif_mps, unit, diag);
  CheckVifClockingExpr(s->var_init, vifs, vif_mps, unit, diag);
  for (const auto* sub : s->stmts)
    WalkStmtsForVifClocking(sub, vifs, vif_mps, unit, diag);
  WalkStmtsForVifClocking(s->then_branch, vifs, vif_mps, unit, diag);
  WalkStmtsForVifClocking(s->else_branch, vifs, vif_mps, unit, diag);
  WalkStmtsForVifClocking(s->body, vifs, vif_mps, unit, diag);
  WalkStmtsForVifClocking(s->for_body, vifs, vif_mps, unit, diag);
  for (auto& ci : s->case_items) {
    WalkStmtsForVifClocking(ci.body, vifs, vif_mps, unit, diag);
  }
}

// Checks one assignment-pattern element `elem` of an array-of-virtual-interface
// initializer against the declared element interface type `iface_type`, using
// the elaborator's interface-instance and virtual-interface type maps.
void CheckArrayOfVifInitElement(const Expr* elem, std::string_view iface_type,
                                const VifTypeMap& interface_inst_types,
                                const VifTypeMap& vi_var_interface_types,
                                DiagEngine& diag) {
  if (!elem) return;
  if (elem->kind != ExprKind::kIdentifier) return;
  auto inst_it = interface_inst_types.find(elem->text);
  if (inst_it != interface_inst_types.end()) {
    if (inst_it->second != iface_type) {
      diag.Error(
          elem->range.start,
          std::format("interface instance '{}' of type '{}' is not compatible "
                      "with virtual interface element type '{}'",
                      elem->text, inst_it->second, iface_type));
    }
    return;
  }
  auto vif_it = vi_var_interface_types.find(elem->text);
  if (vif_it != vi_var_interface_types.end()) {
    if (vif_it->second != iface_type) {
      diag.Error(
          elem->range.start,
          std::format("virtual interface '{}' of type '{}' is not compatible "
                      "with element type '{}'",
                      elem->text, vif_it->second, iface_type));
    }
  }
}

}  // namespace

void Elaborator::ValidateArrayOfVifInitStmt(const Stmt* s) {
  if (!s || s->kind != StmtKind::kVarDecl) return;
  if (!s->var_init) return;
  if (s->var_init->kind != ExprKind::kAssignmentPattern) return;
  std::string_view iface_type =
      ResolveVifInterfaceType(s->var_decl_type, typedefs_);
  if (iface_type.empty()) return;
  if (s->var_unpacked_dims.empty()) return;

  auto size_opt = ComputeDimSize(s->var_unpacked_dims.front());
  if (size_opt &&
      static_cast<int64_t>(s->var_init->elements.size()) != *size_opt) {
    diag_.Error(
        s->var_init->range.start,
        std::format(
            "array-of-virtual-interface initializer has {} elements but "
            "'{}' has size {}",
            s->var_init->elements.size(), s->var_name, *size_opt));
  }

  for (const auto* elem : s->var_init->elements) {
    CheckArrayOfVifInitElement(elem, iface_type, interface_inst_types_,
                               vi_var_interface_types_, diag_);
  }
}

static void WalkStmtsForArrayOfVifInit(const Stmt* s, Elaborator* elab) {
  if (!s) return;
  elab->ValidateArrayOfVifInitStmt(s);
  for (const auto* sub : s->stmts) WalkStmtsForArrayOfVifInit(sub, elab);
  WalkStmtsForArrayOfVifInit(s->then_branch, elab);
  WalkStmtsForArrayOfVifInit(s->else_branch, elab);
  WalkStmtsForArrayOfVifInit(s->body, elab);
  WalkStmtsForArrayOfVifInit(s->for_body, elab);
  for (auto& ci : s->case_items) WalkStmtsForArrayOfVifInit(ci.body, elab);
}

void Elaborator::WalkStmtsForVirtualInterfaceClocking(const Stmt* s) {
  WalkStmtsForArrayOfVifInit(s, this);
}

void Elaborator::ValidateVirtualInterfaceClocking(const ModuleDecl* decl) {
  VifTypeMap module_vifs = vi_var_interface_types_;
  VifModportMap module_mps = vi_var_modports_;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      auto [scoped, scoped_mps] =
          BuildScopedVifMaps(item, module_vifs, module_mps, typedefs_);
      if (item->body) {
        WalkStmtsForVifClocking(item->body, scoped, scoped_mps, unit_, diag_);
        WalkStmtsForVirtualInterfaceClocking(item->body);
      }
    } else {
      bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                     item->kind == ModuleItemKind::kAlwaysCombBlock ||
                     item->kind == ModuleItemKind::kAlwaysFFBlock ||
                     item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                     item->kind == ModuleItemKind::kInitialBlock ||
                     item->kind == ModuleItemKind::kFinalBlock;
      if (is_proc && item->body) {
        WalkStmtsForVifClocking(item->body, module_vifs, module_mps, unit_,
                                diag_);
        WalkStmtsForVirtualInterfaceClocking(item->body);
      }
    }
  }
}

namespace {

using IfacePortTypeMap = std::unordered_map<std::string_view, std::string_view>;
using IfacePortModportMap =
    std::unordered_map<std::string_view, std::string_view>;

const ModuleDecl* LookupInterfaceDecl(const CompilationUnit* unit,
                                      std::string_view name) {
  if (!unit) return nullptr;
  for (const auto* i : unit->interfaces) {
    if (i && i->name == name) return i;
  }
  for (const auto* m : unit->modules) {
    if (m && m->name == name && m->decl_kind == ModuleDeclKind::kInterface) {
      return m;
    }
  }
  return nullptr;
}

bool IsListableInModport(ModuleItemKind kind) {
  switch (kind) {
    case ModuleItemKind::kNetDecl:
    case ModuleItemKind::kVarDecl:
    case ModuleItemKind::kTaskDecl:
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kClockingBlock:
      return true;
    default:
      return false;
  }
}

const ModuleItem* FindInterfaceItemByName(const ModuleDecl* iface,
                                          std::string_view name) {
  if (!iface) return nullptr;
  for (const auto* it : iface->items) {
    if (it && it->name == name) return it;
  }
  return nullptr;
}

bool ModportListsMember(const ModportDecl* mp, std::string_view name) {
  if (!mp) return false;
  for (const auto& p : mp->ports) {
    if (p.name == name) return true;
  }
  return false;
}

const ModportDecl* FindModport(const ModuleDecl* iface,
                               std::string_view modport_name) {
  if (!iface || modport_name.empty()) return nullptr;
  for (const auto* mp : iface->modports) {
    if (mp && mp->name == modport_name) return mp;
  }
  return nullptr;
}

// Diagnoses a `base.member` access expression `e` against the interface-port
// and virtual-interface modport maps: if `base` resolves to a modport-scoped
// interface and `member` is a modport-listable item not exposed by that
// modport, reports the inaccessibility error.
void CheckInterfaceObjectMemberAccess(const Expr* e,
                                      const IfacePortTypeMap& iface_ports,
                                      const IfacePortModportMap& port_mps,
                                      const VifTypeMap& vifs,
                                      const VifModportMap& vif_mps,
                                      const CompilationUnit* unit,
                                      DiagEngine& diag) {
  auto base_name = e->lhs->text;
  auto member_name = e->rhs->text;

  std::string_view iface_type;
  std::string_view modport_name;
  bool bound = false;

  auto pit = iface_ports.find(base_name);
  if (pit != iface_ports.end()) {
    iface_type = pit->second;
    auto mp_it = port_mps.find(base_name);
    if (mp_it != port_mps.end()) modport_name = mp_it->second;
    bound = true;
  } else {
    auto vit = vifs.find(base_name);
    if (vit != vifs.end()) {
      iface_type = vit->second;
      auto mp_it = vif_mps.find(base_name);
      if (mp_it != vif_mps.end()) modport_name = mp_it->second;
      bound = true;
    }
  }

  if (!bound || modport_name.empty() || member_name.empty()) return;
  const auto* iface = LookupInterfaceDecl(unit, iface_type);
  const auto* mp = FindModport(iface, modport_name);
  if (!iface || !mp) return;
  const auto* member = FindInterfaceItemByName(iface, member_name);
  if (member && IsListableInModport(member->kind) &&
      member->kind != ModuleItemKind::kClockingBlock &&
      !ModportListsMember(mp, member_name)) {
    diag.Error(
        e->range.start,
        std::format(
            "'{}' is not accessible through modport '{}' of interface '{}'",
            member_name, modport_name, iface_type));
  }
}

void CheckInterfaceObjectAccessExpr(const Expr* e,
                                    const IfacePortTypeMap& iface_ports,
                                    const IfacePortModportMap& port_mps,
                                    const VifTypeMap& vifs,
                                    const VifModportMap& vif_mps,
                                    const CompilationUnit* unit,
                                    DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->lhs &&
      e->lhs->kind == ExprKind::kIdentifier && e->rhs &&
      e->rhs->kind == ExprKind::kIdentifier) {
    CheckInterfaceObjectMemberAccess(e, iface_ports, port_mps, vifs, vif_mps,
                                     unit, diag);
  }
  CheckInterfaceObjectAccessExpr(e->lhs, iface_ports, port_mps, vifs, vif_mps,
                                 unit, diag);
  CheckInterfaceObjectAccessExpr(e->rhs, iface_ports, port_mps, vifs, vif_mps,
                                 unit, diag);
  CheckInterfaceObjectAccessExpr(e->base, iface_ports, port_mps, vifs, vif_mps,
                                 unit, diag);
  CheckInterfaceObjectAccessExpr(e->index, iface_ports, port_mps, vifs, vif_mps,
                                 unit, diag);
  CheckInterfaceObjectAccessExpr(e->condition, iface_ports, port_mps, vifs,
                                 vif_mps, unit, diag);
  CheckInterfaceObjectAccessExpr(e->true_expr, iface_ports, port_mps, vifs,
                                 vif_mps, unit, diag);
  CheckInterfaceObjectAccessExpr(e->false_expr, iface_ports, port_mps, vifs,
                                 vif_mps, unit, diag);
  for (const auto* elem : e->elements) {
    CheckInterfaceObjectAccessExpr(elem, iface_ports, port_mps, vifs, vif_mps,
                                   unit, diag);
  }
  for (const auto* arg : e->args) {
    CheckInterfaceObjectAccessExpr(arg, iface_ports, port_mps, vifs, vif_mps,
                                   unit, diag);
  }
}

void WalkStmtsForInterfaceObjectAccess(const Stmt* s,
                                       const IfacePortTypeMap& iface_ports,
                                       const IfacePortModportMap& port_mps,
                                       const VifTypeMap& vifs,
                                       const VifModportMap& vif_mps,
                                       const CompilationUnit* unit,
                                       DiagEngine& diag);

// Runs the interface-object-access check on every expression field carried
// directly by statement `s`.
void CheckInterfaceObjectAccessStmtExprs(const Stmt* s,
                                         const IfacePortTypeMap& iface_ports,
                                         const IfacePortModportMap& port_mps,
                                         const VifTypeMap& vifs,
                                         const VifModportMap& vif_mps,
                                         const CompilationUnit* unit,
                                         DiagEngine& diag) {
  CheckInterfaceObjectAccessExpr(s->lhs, iface_ports, port_mps, vifs, vif_mps,
                                 unit, diag);
  CheckInterfaceObjectAccessExpr(s->rhs, iface_ports, port_mps, vifs, vif_mps,
                                 unit, diag);
  CheckInterfaceObjectAccessExpr(s->expr, iface_ports, port_mps, vifs, vif_mps,
                                 unit, diag);
  CheckInterfaceObjectAccessExpr(s->condition, iface_ports, port_mps, vifs,
                                 vif_mps, unit, diag);
  CheckInterfaceObjectAccessExpr(s->var_init, iface_ports, port_mps, vifs,
                                 vif_mps, unit, diag);
}

// Recurses the interface-object-access walk into every child statement of `s`.
void WalkInterfaceObjectAccessChildStmts(const Stmt* s,
                                         const IfacePortTypeMap& iface_ports,
                                         const IfacePortModportMap& port_mps,
                                         const VifTypeMap& vifs,
                                         const VifModportMap& vif_mps,
                                         const CompilationUnit* unit,
                                         DiagEngine& diag) {
  for (const auto* sub : s->stmts) {
    WalkStmtsForInterfaceObjectAccess(sub, iface_ports, port_mps, vifs, vif_mps,
                                      unit, diag);
  }
  WalkStmtsForInterfaceObjectAccess(s->then_branch, iface_ports, port_mps, vifs,
                                    vif_mps, unit, diag);
  WalkStmtsForInterfaceObjectAccess(s->else_branch, iface_ports, port_mps, vifs,
                                    vif_mps, unit, diag);
  WalkStmtsForInterfaceObjectAccess(s->body, iface_ports, port_mps, vifs,
                                    vif_mps, unit, diag);
  WalkStmtsForInterfaceObjectAccess(s->for_body, iface_ports, port_mps, vifs,
                                    vif_mps, unit, diag);
  for (auto& ci : s->case_items) {
    WalkStmtsForInterfaceObjectAccess(ci.body, iface_ports, port_mps, vifs,
                                      vif_mps, unit, diag);
  }
}

void WalkStmtsForInterfaceObjectAccess(const Stmt* s,
                                       const IfacePortTypeMap& iface_ports,
                                       const IfacePortModportMap& port_mps,
                                       const VifTypeMap& vifs,
                                       const VifModportMap& vif_mps,
                                       const CompilationUnit* unit,
                                       DiagEngine& diag) {
  if (!s) return;
  CheckInterfaceObjectAccessStmtExprs(s, iface_ports, port_mps, vifs, vif_mps,
                                      unit, diag);
  WalkInterfaceObjectAccessChildStmts(s, iface_ports, port_mps, vifs, vif_mps,
                                      unit, diag);
}

bool IsProceduralBlockItem(ModuleItemKind kind) {
  return kind == ModuleItemKind::kAlwaysBlock ||
         kind == ModuleItemKind::kAlwaysCombBlock ||
         kind == ModuleItemKind::kAlwaysFFBlock ||
         kind == ModuleItemKind::kAlwaysLatchBlock ||
         kind == ModuleItemKind::kInitialBlock ||
         kind == ModuleItemKind::kFinalBlock;
}

// Runs the interface-object-access checks for one module item, using the
// module-level interface-port and virtual-interface maps. Task/function bodies
// are walked with their formal-argument-scoped maps, continuous assignments are
// checked directly, and procedural blocks are walked with the module maps.
void CheckInterfaceObjectAccessItem(
    const ModuleItem* item, const IfacePortTypeMap& iface_ports,
    const IfacePortModportMap& port_mps, const VifTypeMap& module_vifs,
    const VifModportMap& module_mps, const TypedefMap& typedefs,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (item->kind == ModuleItemKind::kTaskDecl ||
      item->kind == ModuleItemKind::kFunctionDecl) {
    auto [scoped, scoped_mps] =
        BuildScopedVifMaps(item, module_vifs, module_mps, typedefs);
    if (item->body) {
      WalkStmtsForInterfaceObjectAccess(item->body, iface_ports, port_mps,
                                        scoped, scoped_mps, unit, diag);
    }
  } else if (item->kind == ModuleItemKind::kContAssign) {
    CheckInterfaceObjectAccessExpr(item->assign_lhs, iface_ports, port_mps,
                                   module_vifs, module_mps, unit, diag);
    CheckInterfaceObjectAccessExpr(item->assign_rhs, iface_ports, port_mps,
                                   module_vifs, module_mps, unit, diag);
  } else if (IsProceduralBlockItem(item->kind) && item->body) {
    WalkStmtsForInterfaceObjectAccess(item->body, iface_ports, port_mps,
                                      module_vifs, module_mps, unit, diag);
  }
}

}  // namespace

void Elaborator::ValidateInterfaceObjectAccess(const ModuleDecl* decl) {
  if (!decl) return;

  IfacePortTypeMap iface_ports;
  IfacePortModportMap port_mps;
  for (const auto& port : decl->ports) {
    if (port.name.empty()) continue;
    if (port.data_type.kind != DataTypeKind::kNamed) continue;
    const auto* ifc = FindModule(port.data_type.type_name);
    if (!ifc || ifc->decl_kind != ModuleDeclKind::kInterface) continue;
    iface_ports[port.name] = port.data_type.type_name;
    port_mps[port.name] = port.data_type.modport_name;
  }

  if (iface_ports.empty() && vi_var_interface_types_.empty()) return;

  VifTypeMap module_vifs = vi_var_interface_types_;
  VifModportMap module_mps = vi_var_modports_;
  for (const auto* item : decl->items) {
    CheckInterfaceObjectAccessItem(item, iface_ports, port_mps, module_vifs,
                                   module_mps, typedefs_, unit_, diag_);
  }
}

void Elaborator::ValidateInterconnectContAssign(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kContAssign) return;

  if (item->assign_lhs && item->assign_lhs->kind == ExprKind::kIdentifier &&
      interconnect_names_.count(item->assign_lhs->text)) {
    diag_.Error(item->loc,
                "interconnect net cannot be used in continuous assignment");
  }

  if (ExprUsesInterconnect(item->assign_rhs, interconnect_names_)) {
    diag_.Error(item->loc, "interconnect net cannot be used in expression");
  }
}

}  // namespace delta
