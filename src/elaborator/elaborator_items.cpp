#include <algorithm>
#include <cstdlib>
#include <format>
#include <optional>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

void Elaborator::ValidateElabSystemTask(const ModuleItem* item) {
  auto* expr = item->init_expr;
  if (!expr || expr->kind != ExprKind::kSystemCall) return;
  if (expr->callee != "$fatal") return;
  if (expr->args.empty()) return;
  auto* first_arg = expr->args[0];
  if (first_arg->kind == ExprKind::kIntegerLiteral) {
    auto val = first_arg->int_val;
    if (val > 2) {
      diag_.Error(first_arg->range.start,
                  "finish_number must be 0, 1, or 2");
    }
  }
}

// §6.20.5: Elaborate a specparam as a simulation-accessible constant variable.
void Elaborator::ElaborateSpecparam(ModuleItem* item, RtlirModule* mod) {
  RtlirVariable var;
  var.name = ScopedName(item->name);
  if (item->data_type.packed_dim_left && item->data_type.packed_dim_right) {
    var.width = EvalTypeWidth(item->data_type);
    if (var.width == 0) var.width = 32;
  } else {
    var.width = 32;
  }
  var.init_expr = item->init_expr;
  mod->variables.push_back(var);
}

// §6.10: Check if an identifier is already declared as a variable, net, or
// port.
static bool IsNameDeclared(std::string_view name, const RtlirModule* mod) {
  for (const auto& v : mod->variables) {
    if (v.name == name) return true;
  }
  for (const auto& n : mod->nets) {
    if (n.name == name) return true;
  }
  for (const auto& p : mod->ports) {
    if (p.name == name) return true;
  }
  return false;
}

static uint32_t FindSignalWidth(std::string_view name, const RtlirModule* mod) {
  for (const auto& v : mod->variables) {
    if (v.name == name) return v.width;
  }
  for (const auto& n : mod->nets) {
    if (n.name == name) return n.width;
  }
  for (const auto& p : mod->ports) {
    if (p.name == name) return p.width;
  }
  return 0;
}

static NetType FindSignalNetType(std::string_view name,
                                 const RtlirModule* mod) {
  for (const auto& n : mod->nets) {
    if (n.name == name) return n.net_type;
  }
  return NetType::kNone;
}

static DataTypeKind NormalizeForCompatibility(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kWire:
    case DataTypeKind::kTri:
    case DataTypeKind::kWand:
    case DataTypeKind::kTriand:
    case DataTypeKind::kWor:
    case DataTypeKind::kTrior:
    case DataTypeKind::kTri0:
    case DataTypeKind::kTri1:
    case DataTypeKind::kTrireg:
    case DataTypeKind::kSupply0:
    case DataTypeKind::kSupply1:
    case DataTypeKind::kUwire:
      return DataTypeKind::kLogic;
    default:
      return kind;
  }
}

static int NetTypeGroup(NetType t) {
  switch (t) {
    case NetType::kWire:
    case NetType::kTri: return 0;
    case NetType::kWand:
    case NetType::kTriand: return 1;
    case NetType::kWor:
    case NetType::kTrior: return 2;
    case NetType::kTrireg: return 3;
    case NetType::kTri0: return 4;
    case NetType::kTri1: return 5;
    case NetType::kUwire: return 6;
    case NetType::kSupply0: return 7;
    case NetType::kSupply1: return 8;
    default: return -1;
  }
}

static bool DissimilarNetTypeRequiresWarning(NetType internal,
                                             NetType external) {
  static constexpr bool kWarnTable[9][9] = {
      // ext: wire  wand   wor  trireg tri0   tri1  uwire  sup0   sup1
      {false, false, false, false, false, false, false, false, false},  // wire
      {false, false, true,  true,  true,  true,  true,  false, false},  // wand
      {false, true,  false, true,  true,  true,  true,  false, false},  // wor
      {false, true,  true,  false, false, false, true,  false, false},  // trireg
      {false, true,  true,  false, false, true,  true,  false, false},  // tri0
      {false, true,  true,  false, true,  false, true,  false, false},  // tri1
      {false, true,  true,  true,  true,  true,  false, false, false},  // uwire
      {false, false, false, false, false, false, false, false, true},   // supply0
      {false, false, false, false, false, false, false, true,  false},  // supply1
  };
  int ig = NetTypeGroup(internal);
  int eg = NetTypeGroup(external);
  if (ig < 0 || eg < 0) return false;
  return kWarnTable[ig][eg];
}

static NetType PortNetType(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kWire: return NetType::kWire;
    case DataTypeKind::kTri: return NetType::kTri;
    case DataTypeKind::kWand: return NetType::kWand;
    case DataTypeKind::kTriand: return NetType::kTriand;
    case DataTypeKind::kWor: return NetType::kWor;
    case DataTypeKind::kTrior: return NetType::kTrior;
    case DataTypeKind::kTri0: return NetType::kTri0;
    case DataTypeKind::kTri1: return NetType::kTri1;
    case DataTypeKind::kTrireg: return NetType::kTrireg;
    case DataTypeKind::kSupply0: return NetType::kSupply0;
    case DataTypeKind::kSupply1: return NetType::kSupply1;
    case DataTypeKind::kUwire: return NetType::kUwire;
    default: return NetType::kNone;
  }
}

namespace {

struct ScopeWalk {
  std::vector<std::pair<std::string_view, SourceLoc>> block_labels;
  std::unordered_set<std::string_view> local_names;
  std::vector<std::pair<std::string_view, SourceLoc>> proc_lhs;
};

void CollectScopeWalk(const Stmt* s, ScopeWalk& out) {
  if (!s) return;
  if (s->kind == StmtKind::kBlock && !s->label.empty()) {
    out.block_labels.emplace_back(s->label, s->range.start);
  }
  if (s->kind == StmtKind::kVarDecl && !s->var_name.empty()) {
    out.local_names.insert(s->var_name);
  }
  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && s->lhs->kind == ExprKind::kIdentifier) {
    out.proc_lhs.emplace_back(s->lhs->text, s->range.start);
  }
  for (const auto* sub : s->stmts) CollectScopeWalk(sub, out);
  for (const auto* sub : s->fork_stmts) CollectScopeWalk(sub, out);
  CollectScopeWalk(s->then_branch, out);
  CollectScopeWalk(s->else_branch, out);
  CollectScopeWalk(s->body, out);
  CollectScopeWalk(s->for_body, out);
  for (const auto* fi : s->for_inits) CollectScopeWalk(fi, out);
  for (const auto* fs : s->for_steps) CollectScopeWalk(fs, out);
  for (const auto& ci : s->case_items) CollectScopeWalk(ci.body, out);
}

bool IsProcBodyItem(ModuleItemKind k) {
  return k == ModuleItemKind::kInitialBlock ||
         k == ModuleItemKind::kFinalBlock ||
         k == ModuleItemKind::kAlwaysBlock ||
         k == ModuleItemKind::kAlwaysCombBlock ||
         k == ModuleItemKind::kAlwaysFFBlock ||
         k == ModuleItemKind::kAlwaysLatchBlock;
}

}  // namespace

namespace {

void WalkExprIdents(const Expr* e,
                    std::vector<const Expr*>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kIdentifier) {
    out.push_back(e);
    return;
  }
  if (e->kind == ExprKind::kMemberAccess) {
    WalkExprIdents(e->lhs, out);
    return;
  }
  WalkExprIdents(e->lhs, out);
  WalkExprIdents(e->rhs, out);
  WalkExprIdents(e->base, out);
  WalkExprIdents(e->index, out);
  WalkExprIdents(e->index_end, out);
  WalkExprIdents(e->condition, out);
  WalkExprIdents(e->true_expr, out);
  WalkExprIdents(e->false_expr, out);
  WalkExprIdents(e->repeat_count, out);
  WalkExprIdents(e->with_expr, out);
  for (const auto* a : e->args) WalkExprIdents(a, out);
  for (const auto* el : e->elements) WalkExprIdents(el, out);
}

void WalkStmtIdents(const Stmt* s, std::vector<const Expr*>& out) {
  if (!s) return;
  WalkExprIdents(s->condition, out);
  WalkExprIdents(s->lhs, out);
  WalkExprIdents(s->rhs, out);
  WalkExprIdents(s->delay, out);
  WalkExprIdents(s->cycle_delay, out);
  WalkExprIdents(s->for_cond, out);
  WalkExprIdents(s->expr, out);
  WalkExprIdents(s->assert_expr, out);
  WalkExprIdents(s->repeat_event_count, out);
  WalkExprIdents(s->var_init, out);
  for (const auto* e : s->wait_order_events) WalkExprIdents(e, out);
  for (const auto& ci : s->case_items) {
    for (const auto* p : ci.patterns) WalkExprIdents(p, out);
    WalkStmtIdents(ci.body, out);
  }
  for (const auto& [w, body] : s->randcase_items) {
    WalkExprIdents(w, out);
    WalkStmtIdents(body, out);
  }
  for (const auto* sub : s->stmts) WalkStmtIdents(sub, out);
  for (const auto* sub : s->fork_stmts) WalkStmtIdents(sub, out);
  WalkStmtIdents(s->then_branch, out);
  WalkStmtIdents(s->else_branch, out);
  WalkStmtIdents(s->body, out);
  WalkStmtIdents(s->for_body, out);
  for (const auto* fi : s->for_inits) WalkStmtIdents(fi, out);
  for (const auto* fs : s->for_steps) WalkStmtIdents(fs, out);
  WalkStmtIdents(s->assert_pass_stmt, out);
  WalkStmtIdents(s->assert_fail_stmt, out);
}

}  // namespace

void Elaborator::ValidatePackageImportRules(const ModuleDecl* decl) {
  explicit_imports_.clear();
  wildcard_packages_.clear();
  wildcard_claimed_.clear();

  auto provides = [&](std::string_view pkg_name,
                      std::string_view name) -> bool {
    auto it = pkg_provided_names_.find(pkg_name);
    if (it == pkg_provided_names_.end()) {
      auto& s = pkg_provided_names_[pkg_name];
      for (const auto* pkg : unit_->packages) {
        if (pkg->name != pkg_name) continue;
        for (const auto* pi : pkg->items) {
          if (!pi->name.empty()) s.insert(pi->name);
          if (pi->kind == ModuleItemKind::kClassDecl && pi->class_decl &&
              !pi->class_decl->name.empty()) {
            s.insert(pi->class_decl->name);
          }
        }
      }
      it = pkg_provided_names_.find(pkg_name);
    }
    return it->second.count(name) != 0;
  };

  std::unordered_set<std::string_view> seen_decls;
  for (const auto& port : decl->ports) {
    if (!port.name.empty()) seen_decls.insert(port.name);
  }
  for (const auto& [pname, pval] : decl->params) {
    if (!pname.empty()) seen_decls.insert(pname);
  }

  auto track_decl = [&](std::string_view name, SourceLoc loc) {
    if (name.empty()) return;
    auto wit = wildcard_claimed_.find(name);
    if (wit != wildcard_claimed_.end()) {
      diag_.Error(loc,
                  std::format("declaration of '{}' follows a reference "
                              "resolved through a wildcard package import",
                              name));
    }
    seen_decls.insert(name);
  };

  auto process_ref = [&](const Expr* e) {
    auto name = e->text;
    if (name.empty()) return;
    if (seen_decls.count(name)) return;
    std::vector<std::string_view> providers;
    for (auto pkg : wildcard_packages_) {
      if (provides(pkg, name)) providers.push_back(pkg);
    }
    if (providers.size() > 1) {
      diag_.Error(
          e->range.start,
          std::format("reference to '{}' is ambiguous between wildcard "
                      "imports of packages '{}' and '{}'",
                      name, providers[0], providers[1]));
      return;
    }
    if (providers.size() == 1) {
      wildcard_claimed_[name] = e->range.start;
      seen_decls.insert(name);
    }
  };

  for (const auto* item : decl->items) {
    switch (item->kind) {
      case ModuleItemKind::kImportDecl: {
        auto pkg_name = item->import_item.package_name;
        if (item->import_item.is_wildcard) {
          if (std::find(wildcard_packages_.begin(),
                        wildcard_packages_.end(),
                        pkg_name) == wildcard_packages_.end()) {
            wildcard_packages_.push_back(pkg_name);
          }
          break;
        }
        auto name = item->import_item.item_name;
        auto eit = explicit_imports_.find(name);
        if (eit != explicit_imports_.end()) {
          if (eit->second.first == pkg_name) break;
          diag_.Error(
              item->loc,
              std::format("explicit import of '{}::{}' conflicts with earlier "
                          "explicit import from '{}'",
                          pkg_name, name, eit->second.first));
          break;
        }
        if (seen_decls.count(name)) {
          diag_.Error(
              item->loc,
              std::format("explicit import of '{}::{}' collides with "
                          "existing declaration of '{}'",
                          pkg_name, name, name));
          break;
        }
        explicit_imports_[name] = {pkg_name, item->loc};
        seen_decls.insert(name);
        break;
      }
      case ModuleItemKind::kInitialBlock:
      case ModuleItemKind::kFinalBlock:
      case ModuleItemKind::kAlwaysBlock:
      case ModuleItemKind::kAlwaysCombBlock:
      case ModuleItemKind::kAlwaysFFBlock:
      case ModuleItemKind::kAlwaysLatchBlock: {
        std::vector<const Expr*> refs;
        WalkStmtIdents(item->body, refs);
        for (const auto* e : refs) process_ref(e);
        break;
      }
      case ModuleItemKind::kContAssign: {
        std::vector<const Expr*> refs;
        WalkExprIdents(item->assign_lhs, refs);
        WalkExprIdents(item->assign_rhs, refs);
        for (const auto* e : refs) process_ref(e);
        break;
      }
      case ModuleItemKind::kModuleInst:
        track_decl(item->inst_name, item->loc);
        break;
      case ModuleItemKind::kGateInst:
      case ModuleItemKind::kUdpInst:
        track_decl(item->gate_inst_name, item->loc);
        break;
      case ModuleItemKind::kClassDecl:
        if (item->class_decl) track_decl(item->class_decl->name, item->loc);
        break;
      default:
        track_decl(item->name, item->loc);
        break;
    }
  }
}

void Elaborator::ValidateScopeRules(const ModuleDecl* decl) {
  ScopeWalk walk;
  for (const auto* item : decl->items) {
    if (IsProcBodyItem(item->kind)) {
      CollectScopeWalk(item->body, walk);
    }
  }
  for (const auto& [label, loc] : walk.block_labels) {
    if (!declared_names_.insert(label).second) {
      diag_.Error(loc, std::format("redeclaration of '{}'", label));
    }
  }
  for (const auto& [name, loc] : walk.proc_lhs) {
    if (walk.local_names.count(name)) continue;
    if (declared_names_.count(name)) continue;
    if (ansi_port_names_.count(name)) continue;
    if (non_ansi_complete_ports_.count(name)) continue;
    if (non_ansi_partial_ports_.count(name)) continue;
    if (const_names_.count(name)) continue;
    if (enum_member_names_.count(name)) continue;
    if (specparam_names_.count(name)) continue;
    if (class_names_.count(name)) continue;
    if (class_var_names_.count(name)) continue;
    if (task_names_.count(name)) continue;
    if (func_decls_.count(name)) continue;
    if (interface_inst_types_.count(name)) continue;
    if (checker_inst_names_.count(name)) continue;
    diag_.Error(loc, std::format("undeclared identifier '{}'", name));
  }
}

bool Elaborator::MaybeCreateImplicitNet(std::string_view name, SourceLoc loc,
                                        RtlirModule* mod) {
  if (IsNameDeclared(name, mod)) return true;
  if (unit_->default_nettype == NetType::kNone) {
    diag_.Error(loc, std::format("implicit net '{}' forbidden by "
                                 "`default_nettype none",
                                 name));
    return false;
  }
  RtlirNet net;
  net.name = ScopedName(name);
  net.net_type = unit_->default_nettype;
  net.width = 1;  // §6.10: Implicit nets are scalar.
  mod->nets.push_back(net);
  declared_names_.insert(name);
  net_names_.insert(name);
  return true;
}

// §10.3.2: Validate identifier-based continuous assignment targets.
void Elaborator::ValidateContAssignIdentLhs(ModuleItem* item,
                                            RtlirModule* mod) {
  auto name = item->assign_lhs->text;
  MaybeCreateImplicitNet(name, item->loc, mod);
  if (!cont_assign_targets_.emplace(name, item->loc).second) {
    if (net_names_.count(name) == 0) {
      diag_.Error(item->loc,
                  std::format("multiple continuous assignments to '{}'", name));
    } else {
      auto it = var_types_.find(name);
      if (it != var_types_.end() && it->second == DataTypeKind::kUwire) {
        diag_.Error(item->loc,
                    std::format("uwire '{}' cannot have multiple drivers", name));
      }
    }
  }
  if (var_init_names_.count(name) != 0) {
    diag_.Error(item->loc,
                std::format("variable '{}' has both an initializer and a "
                            "continuous assignment",
                            name));
  }
}

// §10.3.2/§10.3.3: Validate nettype constraints on continuous assignment.
void Elaborator::ValidateContAssignNettypeAndDelay(ModuleItem* item) {
  if (item->assign_lhs->kind == ExprKind::kSelect) {
    auto* base = item->assign_lhs->base;
    if (base && base->kind == ExprKind::kIdentifier &&
        nettype_net_names_.count(base->text) != 0) {
      diag_.Error(item->loc,
                  "continuous assignment to a nettype net shall not contain "
                  "indexing or select");
    }
  }
  if (item->assign_lhs->kind == ExprKind::kMemberAccess) {
    auto* base = item->assign_lhs->lhs;
    if (base && base->kind == ExprKind::kIdentifier &&
        nettype_net_names_.count(base->text) != 0) {
      diag_.Error(item->loc,
                  "continuous assignment to a nettype net shall not contain "
                  "indexing or select");
    }
  }
  if (item->assign_lhs->kind == ExprKind::kIdentifier &&
      nettype_net_names_.count(item->assign_lhs->text) != 0) {
    if (item->assign_delay_fall || item->assign_delay_decay) {
      diag_.Error(item->loc,
                  "continuous assignment to a nettype net shall have at most "
                  "a single delay");
    }
  }
}

// §10.3.4: Validate drive strength on continuous assignment.
void Elaborator::ValidateContAssignDriveStrength(ModuleItem* item,
                                                 RtlirModule* mod) {
  if (item->assign_lhs->kind != ExprKind::kIdentifier) return;
  uint32_t lhs_width = LookupLhsWidth(item->assign_lhs, mod);
  if (lhs_width <= 1) return;
  bool is_supply = false;
  for (const auto& n : mod->nets) {
    if (n.name == item->assign_lhs->text) {
      is_supply =
          (n.net_type == NetType::kSupply0 || n.net_type == NetType::kSupply1);
      break;
    }
  }
  if (!is_supply) {
    diag_.Error(item->loc,
                "drive strength on continuous assignment applies only to "
                "scalar nets");
  }
}

void Elaborator::ElaborateContAssign(ModuleItem* item, RtlirModule* mod) {
  if (item->assign_lhs && item->assign_lhs->kind == ExprKind::kIdentifier) {
    ValidateContAssignIdentLhs(item, mod);
    // §10.3 Syntax 10-1: The variable form of continuous_assign does not
    // permit drive_strength or delay3.
    bool is_var_target = net_names_.count(item->assign_lhs->text) == 0;
    if (is_var_target) {
      if (item->drive_strength0 != 0 || item->drive_strength1 != 0) {
        diag_.Error(item->loc,
                    "drive strength not allowed on continuous assignment "
                    "to a variable");
      }
      if (item->assign_delay_fall || item->assign_delay_decay) {
        diag_.Error(item->loc,
                    "multiple delays not allowed on continuous assignment "
                    "to a variable");
      }
    }
  }
  if (item->assign_lhs) {
    ValidateContAssignNettypeAndDelay(item);
  }
  if ((item->drive_strength0 != 0 || item->drive_strength1 != 0) &&
      item->assign_lhs) {
    ValidateContAssignDriveStrength(item, mod);
  }
  RtlirContAssign ca;
  ca.lhs = item->assign_lhs;
  ca.rhs = item->assign_rhs;
  ca.width = LookupLhsWidth(ca.lhs, mod);
  ca.drive_strength0 = item->drive_strength0;
  ca.drive_strength1 = item->drive_strength1;
  ca.delay = item->assign_delay;
  ca.delay_fall = item->assign_delay_fall;
  ca.delay_decay = item->assign_delay_decay;
  // §5.12: Resolve attributes.
  ca.attrs = ResolveAttributes(item->attrs, diag_);
  mod->assigns.push_back(ca);
}

void Elaborator::ElaborateParamDecl(ModuleItem* item, RtlirModule* mod) {
  // §6.20.3: Type parameters register as typedefs.
  bool is_type = item->data_type.kind == DataTypeKind::kVoid &&
                 item->typedef_type.kind != DataTypeKind::kImplicit;
  if (is_type) {
    typedefs_[item->name] = item->typedef_type;
  }
  RtlirParamDecl pd;
  pd.name = item->name;
  pd.is_type_param = is_type;
  // §6.20.1: Body parameter becomes localparam when parameter_port_list exists.
  pd.is_localparam = item->is_localparam || mod->has_param_port_list;
  pd.default_value = item->init_expr;
  if (!is_type) {
    PopulateParamTypeInfo(pd, item->data_type);
  }
  // §6.20.7: detect $ as unbounded parameter value.
  if (item->init_expr && item->init_expr->kind == ExprKind::kIdentifier &&
      item->init_expr->text == "$") {
    pd.is_unbounded = true;
  } else if (item->init_expr) {
    auto scope = BuildParamScope(mod);
    auto val = ConstEvalInt(item->init_expr, scope);
    if (val) {
      pd.resolved_value = *val;
      pd.is_resolved = true;
    }
  }
  mod->params.push_back(pd);
  // §6.20: Constants are named data objects that never change.
  const_names_.insert(item->name);
}

void Elaborator::ElaborateItem(ModuleItem* item, RtlirModule* mod) {
  switch (item->kind) {
    case ModuleItemKind::kNetDecl:
      ElaborateNetDecl(item, mod);
      break;
    case ModuleItemKind::kVarDecl:
      ElaborateVarDecl(item, mod);
      break;
    case ModuleItemKind::kContAssign:
      ElaborateContAssign(item, mod);
      break;
    case ModuleItemKind::kInitialBlock:
      AddProcess(RtlirProcessKind::kInitial, item, mod, arena_, diag_);
      break;
    case ModuleItemKind::kFinalBlock:
      AddProcess(RtlirProcessKind::kFinal, item, mod, arena_, diag_);
      break;
    case ModuleItemKind::kAlwaysBlock:
    case ModuleItemKind::kAlwaysCombBlock:
    case ModuleItemKind::kAlwaysFFBlock:
    case ModuleItemKind::kAlwaysLatchBlock:
      AddProcess(MapAlwaysKind(item->always_kind), item, mod, arena_, diag_,
                 &func_decls_);
      break;
    case ModuleItemKind::kModuleInst:
      ElaborateModuleInst(item, mod);
      break;
    case ModuleItemKind::kParamDecl:
      ElaborateParamDecl(item, mod);
      break;
    case ModuleItemKind::kGenerateIf:
    case ModuleItemKind::kGenerateCase:
    case ModuleItemKind::kGenerateFor:
      pending_generates_.push_back({item, mod});
      break;
    case ModuleItemKind::kTypedef:
      ElaborateTypedef(item, mod);
      break;
    case ModuleItemKind::kNettypeDecl:
      ElaborateNettypeDecl(item, mod);
      break;
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kTaskDecl:
      // §23.9: Task/function names share the same scope as variables/nets.
      if (!item->name.empty() &&
          !declared_names_.insert(item->name).second) {
        diag_.Error(item->loc,
                    std::format("redeclaration of '{}'", item->name));
      }
      ValidateFunctionBody(item);
      mod->function_decls.push_back(item);
      break;
    case ModuleItemKind::kGateInst:
      // §23.9: A gate instance name cannot be the same as its output net.
      if (!item->gate_inst_name.empty() && !item->gate_terminals.empty() &&
          item->gate_terminals[0] &&
          item->gate_terminals[0]->kind == ExprKind::kIdentifier &&
          item->gate_terminals[0]->text == item->gate_inst_name) {
        diag_.Error(item->loc,
                    std::format("gate instance name '{}' conflicts with its "
                                "output net",
                                item->gate_inst_name));
      }
      // §23.9: Gate instance names occupy the enclosing scope's name space.
      if (!item->gate_inst_name.empty() &&
          !declared_names_.insert(item->gate_inst_name).second) {
        diag_.Error(item->loc,
                    std::format("redeclaration of '{}'",
                                item->gate_inst_name));
      }
      ElaborateGateInst(item, mod, arena_);
      ResolveInterconnectPrimitiveTerminals(item->gate_terminals, mod);
      break;
    case ModuleItemKind::kUdpInst:
      // §23.9: UDP instance names occupy the enclosing scope's name space.
      if (!item->gate_inst_name.empty() &&
          !declared_names_.insert(item->gate_inst_name).second) {
        diag_.Error(item->loc,
                    std::format("redeclaration of '{}'",
                                item->gate_inst_name));
      }
      ResolveInterconnectPrimitiveTerminals(item->gate_terminals, mod);
      break;
    case ModuleItemKind::kSpecparam:
      specparam_names_.insert(item->name);
      const_names_.insert(item->name);
      ElaborateSpecparam(item, mod);
      break;
    case ModuleItemKind::kAlias: {
      for (auto* net : item->alias_nets) {
        if (net && net->kind == ExprKind::kIdentifier) {
          MaybeCreateImplicitNet(net->text, item->loc, mod);
        }
      }
      ValidateAlias(item, mod);
      RtlirAlias alias;
      alias.nets = item->alias_nets;
      mod->aliases.push_back(alias);
      break;
    }
    case ModuleItemKind::kSequenceDecl:
      sequence_names_.insert(item->name);
      mod->sequence_decls.push_back(item);
      ValidateClockingBlock(item);
      break;
    case ModuleItemKind::kDefparam:
      break;
    case ModuleItemKind::kImportDecl: {
      // §23.7: Collect import declarations for dotted name resolution.
      RtlirImport imp;
      imp.package_name = item->import_item.package_name;
      imp.item_name = item->import_item.item_name;
      imp.is_wildcard = item->import_item.is_wildcard;
      mod->imports.push_back(imp);
      break;
    }
    case ModuleItemKind::kExportDecl:
    case ModuleItemKind::kPropertyDecl:
    case ModuleItemKind::kAssertProperty:
    case ModuleItemKind::kAssumeProperty:
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
    case ModuleItemKind::kRestrictProperty:
    case ModuleItemKind::kClockingBlock:
      ValidateClockingBlock(item);
      break;
    case ModuleItemKind::kElabSystemTask:
      ValidateElabSystemTask(item);
      break;
    case ModuleItemKind::kCovergroupDecl:
    case ModuleItemKind::kSpecifyBlock:
    case ModuleItemKind::kDpiImport:
    case ModuleItemKind::kDpiExport:
    case ModuleItemKind::kLetDecl:
      mod->let_decls.push_back(item);
      break;
    case ModuleItemKind::kDefaultDisableIff:
    case ModuleItemKind::kNestedModuleDecl:
      break;
    case ModuleItemKind::kClassDecl:
      if (item->class_decl) {
        class_names_.insert(item->class_decl->name);
        if (!item->class_decl->params.empty())
          parameterized_class_names_.insert(item->class_decl->name);
        mod->class_decls.push_back(item->class_decl);
      }
      break;
  }
}

void Elaborator::ElaborateTypedef(ModuleItem* item, RtlirModule* mod) {
  typedefs_[item->name] = item->typedef_type;
  if (item->typedef_type.kind == DataTypeKind::kStruct ||
      item->typedef_type.kind == DataTypeKind::kUnion) {
    ValidatePackedStructDefaults(item->typedef_type, item->loc);
    ValidateUnpackedStructWithUnionDefaults(item->typedef_type, item->loc);
    ValidateStructMemberDefaultsConstant(item->typedef_type, item->loc);
    ValidateVoidMembers(item->typedef_type, item->loc);
    ValidateRandQualifiers(item->typedef_type, item->loc);
    ValidatePackedDimRequiresPackedKeyword(item->typedef_type, item->loc);
    ValidatePackedStructMemberTypes(item->typedef_type, item->loc);
    ValidateChandleInUnion(item->typedef_type, item->loc);
    ValidateVirtualInterfaceInUnion(item->typedef_type, item->loc);
    ValidatePackedUnion(item->typedef_type, item->loc);
  }
  ValidatePackedDimOnPredefinedType(item->typedef_type, item->loc);
  if (item->typedef_type.kind != DataTypeKind::kEnum) return;
  ValidateEnumDecl(item->typedef_type, item->loc);
  int64_t next_val = 0;
  auto width = EvalTypeWidth(item->typedef_type, typedefs_);
  std::vector<RtlirEnumMember> members;
  for (const auto& member : item->typedef_type.enum_members) {
    if (member.value) {
      next_val = ConstEvalInt(member.value).value_or(next_val);
    }
    // §6.19.2: Expand range members into concrete named constants.
    if (member.range_start) {
      auto n = ConstEvalInt(member.range_start).value_or(0);
      if (member.range_end) {
        // name[N:M] form: generate nameN, nameN+1, ..., nameM (or decrement).
        auto m = ConstEvalInt(member.range_end).value_or(0);
        int step = (m >= n) ? 1 : -1;
        for (auto i = n;; i += step) {
          auto s = std::format("{}{}", member.name, i);
          auto* p = arena_.AllocString(s.c_str(), s.size());
          std::string_view sv{p, s.size()};
          enum_member_names_.insert(sv);
          members.push_back({sv, next_val});
          RtlirVariable var;
          var.name = sv;
          var.width = width;
          var.is_4state = false;
          mod->variables.push_back(var);
          ++next_val;
          if (i == m) break;
        }
      } else {
        // name[N] form: generate name0, name1, ..., nameN-1.
        for (int64_t i = 0; i < n; ++i) {
          auto s = std::format("{}{}", member.name, i);
          auto* p = arena_.AllocString(s.c_str(), s.size());
          std::string_view sv{p, s.size()};
          enum_member_names_.insert(sv);
          members.push_back({sv, next_val});
          RtlirVariable var;
          var.name = sv;
          var.width = width;
          var.is_4state = false;
          mod->variables.push_back(var);
          ++next_val;
        }
      }
    } else {
      // Plain member (no range).
      enum_member_names_.insert(member.name);
      members.push_back({member.name, next_val});
      RtlirVariable var;
      var.name = member.name;
      var.width = width;
      var.is_4state = false;
      mod->variables.push_back(var);
      ++next_val;
    }
  }
  mod->enum_types[item->name] = std::move(members);
}

// §6.6.7: Register a user-defined nettype so declarations using it create nets.
void Elaborator::ElaborateNettypeDecl(ModuleItem* item, RtlirModule* /*mod*/) {
  typedefs_[item->name] = item->typedef_type;
  nettype_names_.insert(item->name);
  if (!item->nettype_resolve_func.empty()) {
    nettype_resolve_funcs_[item->name] = item->nettype_resolve_func;
    nettype_canonical_[item->name] = item->name;
  } else if (item->typedef_type.kind == DataTypeKind::kNamed) {
    // §6.6.7: Alias form inherits resolution function from base nettype.
    auto it = nettype_resolve_funcs_.find(item->typedef_type.type_name);
    if (it != nettype_resolve_funcs_.end()) {
      nettype_resolve_funcs_[item->name] = it->second;
    }
    // §6.22.6(b): Alias resolves to the base's canonical name.
    auto cit = nettype_canonical_.find(item->typedef_type.type_name);
    nettype_canonical_[item->name] =
        (cit != nettype_canonical_.end()) ? cit->second
                                          : item->typedef_type.type_name;
  } else {
    nettype_canonical_[item->name] = item->name;
  }
}

// §6.22.6: Two nettype names match if they resolve to the same canonical base.
bool Elaborator::NettypesMatch(std::string_view a, std::string_view b) const {
  if (a == b) return true;
  auto ait = nettype_canonical_.find(a);
  auto bit = nettype_canonical_.find(b);
  std::string_view ca = (ait != nettype_canonical_.end()) ? ait->second : a;
  std::string_view cb = (bit != nettype_canonical_.end()) ? bit->second : b;
  return ca == cb;
}

void Elaborator::ElaborateItems(const ModuleDecl* decl, RtlirModule* mod) {
  declared_names_.clear();
  net_names_.clear();
  cont_assign_targets_.clear();
  proc_assign_targets_.clear();
  var_types_.clear();
  var_array_info_.clear();
  specparam_names_.clear();
  enum_var_names_.clear();
  enum_member_names_.clear();
  const_names_.clear();
  class_var_names_.clear();
  class_var_types_.clear();
  var_init_names_.clear();
  output_port_targets_.clear();
  nettype_net_names_.clear();
  interconnect_names_.clear();
  scalar_var_names_.clear();
  var_named_types_.clear();
  alias_pairs_.clear();
  non_ansi_complete_ports_.clear();
  non_ansi_partial_ports_.clear();
  ansi_port_names_.clear();
  clocking_signals_.clear();
  interface_inst_types_.clear();
  vi_var_interface_types_.clear();
  vi_var_modports_.clear();
  checker_inst_names_.clear();
  program_inst_names_.clear();
  auto_task_func_names_.clear();
  nested_module_decls_.clear();
  task_names_.clear();
  sequence_names_.clear();
  func_decls_.clear();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl) {
      nested_module_decls_[item->nested_module_decl->name] =
          item->nested_module_decl;
    }
    // §25.9: virtual interface shall not be used as an interface item.
    if (decl->decl_kind == ModuleDeclKind::kInterface &&
        item->kind == ModuleItemKind::kVarDecl &&
        item->data_type.kind == DataTypeKind::kVirtualInterface) {
      diag_.Error(item->loc,
                  "virtual interface cannot be declared inside an interface");
    }
  }
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kModuleInst) {
      auto* child = FindModuleInScope(item->inst_module);
      if (child && child->decl_kind == ModuleDeclKind::kInterface) {
        interface_inst_types_[item->inst_name] = item->inst_module;
      }
      if (child && child->decl_kind == ModuleDeclKind::kChecker) {
        checker_inst_names_.insert(item->inst_name);
      }
      if (child && child->decl_kind == ModuleDeclKind::kProgram) {
        program_inst_names_.insert(item->inst_name);
      }
      if (decl->decl_kind == ModuleDeclKind::kInterface && child &&
          child->decl_kind == ModuleDeclKind::kModule) {
        diag_.Error(item->loc,
                    std::format("module '{}' cannot be instantiated inside "
                                "interface '{}'",
                                item->inst_module, decl->name));
      }
    }
    // §24.3: Portless nested programs are implicitly instantiated under
    // their declaration name.
    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl &&
        item->nested_module_decl->decl_kind == ModuleDeclKind::kProgram &&
        item->nested_module_decl->ports.empty()) {
      program_inst_names_.insert(item->nested_module_decl->name);
    }
    if (decl->decl_kind == ModuleDeclKind::kInterface &&
        item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl &&
        item->nested_module_decl->decl_kind == ModuleDeclKind::kModule) {
      diag_.Error(item->loc,
                  std::format("module '{}' cannot be declared inside "
                              "interface '{}'",
                              item->nested_module_decl->name, decl->name));
    }
  }
  // §6.20: Parameter port list names are constants that never change.
  for (const auto& [pname, pval] : decl->params) {
    const_names_.insert(pname);
  }
  // §13.2: Collect task names so function body validation can detect task
  // enables. §13.4.3: Collect function declarations for constant function
  // validation.
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl) {
      task_names_.insert(item->name);
    }
    if (item->kind == ModuleItemKind::kFunctionDecl) {
      func_decls_[item->name] = item;
    }
  }
  // §13.4.2: Propagate module default lifetime to functions/tasks without
  // an explicit qualifier.
  for (auto* item : decl->items) {
    if ((item->kind == ModuleItemKind::kFunctionDecl ||
         item->kind == ModuleItemKind::kTaskDecl) &&
        !item->is_automatic && !item->is_static) {
      if (decl->is_automatic) {
        item->is_automatic = true;
      } else {
        item->is_static = true;
      }
    }
  }
  // §23.6 R12: Collect automatic task/function names for hier ref validation.
  for (const auto* item : decl->items) {
    if ((item->kind == ModuleItemKind::kTaskDecl ||
         item->kind == ModuleItemKind::kFunctionDecl) &&
        item->is_automatic) {
      auto_task_func_names_.insert(item->name);
    }
  }
  // §23.4: Save nested module list before the main loop since recursive
  // ElaborateModule calls during child instantiation clear per-module state.
  std::vector<std::pair<std::string_view, ModuleDecl*>> local_nested_modules(
      nested_module_decls_.begin(), nested_module_decls_.end());
  for (auto* item : decl->items) {
    ElaborateItem(item, mod);
  }
  // §23.4: Implicitly instantiate portless nested modules that were not
  // explicitly instantiated.
  // §25.3: Interfaces are never implicitly instantiated.
  for (const auto& [name, nested_decl] : local_nested_modules) {
    if (!nested_decl->ports.empty()) continue;
    if (nested_decl->decl_kind == ModuleDeclKind::kInterface) continue;
    bool explicitly_instantiated = false;
    for (const auto& child : mod->children) {
      if (child.module_name == name) {
        explicitly_instantiated = true;
        break;
      }
    }
    if (explicitly_instantiated) continue;
    RtlirModuleInst inst;
    inst.module_name = name;
    inst.inst_name = name;
    ParamList empty_params;
    inst.resolved = ElaborateModule(nested_decl, empty_params);
    mod->children.push_back(inst);
  }
  // §9.2.2.2: Check for multi-driver violations on always_comb LHS variables.
  CheckAlwaysCombMultiDriver(decl, mod);
  ValidateModuleConstraints(decl);
  ValidateValueParams(decl, mod);
  ValidateClockvarAccess(decl);
  ValidateCycleDelayDefaultClocking(decl);
  ValidateDuplicateDefaultClocking(decl);
  ValidateDuplicateGlobalClocking(decl);
  ValidateContAssignToClockvar(decl);
  ValidateConstantFunctionCalls(decl);
  ValidateSequenceEventArgs(decl);
  ValidateHierRefIntoChecker(decl);
  ValidateHierRefIntoProgram(decl);
  ValidateProgramSubroutineCall(decl);
  ValidateHierRefToAutomatic(decl);
  ValidateHierRefToImportedName(decl, mod);
}

namespace {

void CollectMemberAccess(const Expr* e,
                         std::vector<const Expr*>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess) {
    out.push_back(e);
  }
  CollectMemberAccess(e->lhs, out);
  CollectMemberAccess(e->rhs, out);
  CollectMemberAccess(e->base, out);
  CollectMemberAccess(e->index, out);
  CollectMemberAccess(e->index_end, out);
  CollectMemberAccess(e->condition, out);
  CollectMemberAccess(e->true_expr, out);
  CollectMemberAccess(e->false_expr, out);
  CollectMemberAccess(e->repeat_count, out);
  CollectMemberAccess(e->with_expr, out);
  for (const auto* a : e->args) CollectMemberAccess(a, out);
  for (const auto* el : e->elements) CollectMemberAccess(el, out);
}

void CollectMemberAccessInStmt(const Stmt* s, std::vector<const Expr*>& out) {
  if (!s) return;
  CollectMemberAccess(s->condition, out);
  CollectMemberAccess(s->lhs, out);
  CollectMemberAccess(s->rhs, out);
  CollectMemberAccess(s->delay, out);
  CollectMemberAccess(s->cycle_delay, out);
  CollectMemberAccess(s->for_cond, out);
  CollectMemberAccess(s->expr, out);
  CollectMemberAccess(s->assert_expr, out);
  for (const auto& ci : s->case_items) {
    for (const auto* p : ci.patterns) CollectMemberAccess(p, out);
    CollectMemberAccessInStmt(ci.body, out);
  }
  for (const auto& [w, body] : s->randcase_items) {
    CollectMemberAccess(w, out);
    CollectMemberAccessInStmt(body, out);
  }
  for (const auto* sub : s->stmts) CollectMemberAccessInStmt(sub, out);
  for (const auto* sub : s->fork_stmts) CollectMemberAccessInStmt(sub, out);
  CollectMemberAccessInStmt(s->then_branch, out);
  CollectMemberAccessInStmt(s->else_branch, out);
  CollectMemberAccessInStmt(s->body, out);
  CollectMemberAccessInStmt(s->for_body, out);
  for (const auto* fi : s->for_inits) CollectMemberAccessInStmt(fi, out);
  for (const auto* fs : s->for_steps) CollectMemberAccessInStmt(fs, out);
  CollectMemberAccessInStmt(s->assert_pass_stmt, out);
  CollectMemberAccessInStmt(s->assert_fail_stmt, out);
}

}  // namespace

void Elaborator::ValidateHierRefToImportedName(const ModuleDecl* decl,
                                               const RtlirModule* mod) {
  if (!mod || mod->children.empty()) return;
  std::unordered_map<std::string_view, const RtlirModule*> inst_type;
  for (const auto& child : mod->children) {
    if (child.resolved) inst_type[child.inst_name] = child.resolved;
  }
  if (inst_type.empty()) return;

  auto imported_into = [&](const RtlirModule* m, std::string_view name) {
    for (const auto& imp : m->imports) {
      if (!imp.is_wildcard && imp.item_name == name) return true;
      if (imp.is_wildcard) {
        for (const auto* pkg : unit_->packages) {
          if (pkg->name != imp.package_name) continue;
          for (const auto* pi : pkg->items) {
            if (pi->name == name) return true;
            if (pi->kind == ModuleItemKind::kClassDecl && pi->class_decl &&
                pi->class_decl->name == name)
              return true;
          }
        }
      }
    }
    return false;
  };

  auto check_member_access = [&](const Expr* ma) {
    if (!ma || ma->kind != ExprKind::kMemberAccess) return;
    if (!ma->lhs || ma->lhs->kind != ExprKind::kIdentifier) return;
    if (!ma->rhs || ma->rhs->kind != ExprKind::kIdentifier) return;
    auto it = inst_type.find(ma->lhs->text);
    if (it == inst_type.end()) return;
    if (imported_into(it->second, ma->rhs->text)) {
      diag_.Error(
          ma->range.start,
          std::format("hierarchical reference '{}.{}' targets a name imported "
                      "into '{}' from a package; imported names are not "
                      "visible through hierarchical references",
                      ma->lhs->text, ma->rhs->text, it->second->name));
    }
  };

  std::vector<const Expr*> accesses;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CollectMemberAccess(item->assign_lhs, accesses);
      CollectMemberAccess(item->assign_rhs, accesses);
    }
    if (IsProcBodyItem(item->kind)) {
      CollectMemberAccessInStmt(item->body, accesses);
    }
  }
  for (const auto* ma : accesses) check_member_access(ma);
}

// --- Module instantiation ---

static uint32_t EvalInstDimSize(const Expr* left, const Expr* right) {
  if (left && right) {
    auto lv = ConstEvalInt(left);
    auto rv = ConstEvalInt(right);
    if (lv && rv)
      return static_cast<uint32_t>(std::abs(*lv - *rv) + 1);
  } else if (left) {
    auto v = ConstEvalInt(left);
    if (v && *v > 0) return static_cast<uint32_t>(*v);
  }
  return 0;
}

void Elaborator::ElaborateModuleInst(ModuleItem* item, RtlirModule* mod) {
  // §23.9: Instance names share the enclosing scope's name space.
  if (!item->inst_name.empty() &&
      !declared_names_.insert(item->inst_name).second) {
    diag_.Error(item->loc,
                std::format("redeclaration of '{}'", item->inst_name));
  }
  RtlirModuleInst inst;
  inst.module_name = item->inst_module;
  inst.inst_name = item->inst_name;

  auto* child_decl = FindModuleInScope(item->inst_module);
  if (!child_decl) {
    if (item->inst_scope.empty())
      diag_.Error(item->loc,
                  std::format("unknown module '{}'", item->inst_module));
    else
      diag_.Error(item->loc,
                  std::format("unknown module '{}::{}'", item->inst_scope,
                              item->inst_module));
    mod->children.push_back(inst);
    return;
  }

  auto saved_nested = nested_module_decls_;
  ParamList child_params;
  auto parent_scope = BuildParamScope(mod);

  bool is_positional = false;
  for (const auto& [pname, pexpr] : item->inst_params) {
    if (pname.empty() && pexpr) {
      is_positional = true;
      break;
    }
  }

  if (is_positional) {
    std::vector<std::string_view> targets;
    for (const auto& [dname, dexpr] : child_decl->params) {
      if (child_decl->localparam_port_names.count(dname) > 0) continue;
      targets.push_back(dname);
    }
    if (item->inst_params.size() > targets.size()) {
      diag_.Error(
          item->loc,
          std::format("too many positional parameter overrides for module "
                      "'{}': {} provided, {} allowed",
                      item->inst_module, item->inst_params.size(),
                      targets.size()));
    }
    size_t n = std::min(item->inst_params.size(), targets.size());
    for (size_t i = 0; i < n; ++i) {
      auto* pexpr = item->inst_params[i].second;
      if (!pexpr) continue;
      auto val = ConstEvalInt(pexpr, parent_scope);
      if (val) child_params.push_back({targets[i], *val});
    }
  } else {
    std::unordered_set<std::string_view> overridable;
    for (const auto& [dname, dexpr] : child_decl->params) {
      if (child_decl->localparam_port_names.count(dname) > 0) continue;
      overridable.insert(dname);
    }
    for (const auto& [pname, pexpr] : item->inst_params) {
      if (overridable.count(pname) == 0) {
        diag_.Error(item->loc,
                    std::format("module '{}' has no parameter '{}'",
                                item->inst_module, pname));
        continue;
      }
      if (!pexpr) continue;
      auto val = ConstEvalInt(pexpr, parent_scope);
      if (val) child_params.push_back({pname, *val});
    }
  }
  inst.resolved = ElaborateModule(child_decl, child_params);
  nested_module_decls_ = std::move(saved_nested);
  BindPorts(inst, item, mod);

  std::vector<uint32_t> inst_dim_sizes;
  uint32_t total_instances = 1;
  for (const auto& [left, right] : item->inst_dims) {
    uint32_t sz = EvalInstDimSize(left, right);
    if (sz > 0) {
      inst_dim_sizes.push_back(sz);
      total_instances *= sz;
    }
  }

  if (!item->inst_dims.empty()) {
    ValidateInstanceArrayPorts(inst, item, mod, inst_dim_sizes,
                               total_instances);
  } else {
    ValidateUnpackedArrayPorts(inst, item, mod);
  }

  CheckPortCoercion(inst, item->loc);
  CheckUwirePortMerge(inst, item, mod);
  CheckInterconnectPortMerge(inst, item, mod);
  // §5.12: Resolve attributes.
  inst.attrs = ResolveAttributes(item->attrs, diag_);
  mod->children.push_back(inst);
}

Expr* Elaborator::MakePullExpr(NetType drive) {
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kIntegerLiteral;
  expr->int_val = (drive == NetType::kTri1) ? 1 : 0;
  return expr;
}

Expr* Elaborator::MakeHighZExpr() {
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kUnbasedUnsizedLiteral;
  expr->text = "'z";
  return expr;
}

void Elaborator::BindPorts(RtlirModuleInst& inst, const ModuleItem* item,
                           RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;
  const bool has_pull = unit_->unconnected_drive != NetType::kWire;

  const bool is_ordered =
      !item->inst_ports.empty() && item->inst_ports[0].first.empty();

  for (size_t i = 0; i < item->inst_ports.size(); ++i) {
    auto& [port_name, conn_expr] = item->inst_ports[i];
    const bool is_implicit = i < item->inst_ports_implicit.size() &&
                             item->inst_ports_implicit[i];

    if (conn_expr && conn_expr->kind == ExprKind::kIdentifier) {
      if (is_implicit) {
        if (!IsNameDeclared(conn_expr->text, parent_mod)) {
          diag_.Error(
              item->loc,
              std::format(
                  "implicit named port connection '.{}' requires "
                  "signal '{}' to be declared in the instantiating scope",
                  port_name, conn_expr->text));
        }
      } else if (!interface_inst_types_.count(conn_expr->text)) {
        MaybeCreateImplicitNet(conn_expr->text, item->loc, parent_mod);
      }
    }
    RtlirPortBinding binding;
    binding.connection = conn_expr;

    auto it = child_ports.end();
    if (is_ordered) {
      if (i < child_ports.size()) {
        it = child_ports.begin() + static_cast<ptrdiff_t>(i);
        binding.port_name = it->name;
      } else {
        diag_.Warning(
            item->loc,
            std::format(
                "too many ordered port connections for module '{}'"
                " (expected {}, got {})",
                inst.module_name, child_ports.size(),
                item->inst_ports.size()));
        break;
      }
    } else {
      binding.port_name = port_name;
      it = std::find_if(child_ports.begin(), child_ports.end(),
                         [&](const RtlirPort& p) {
                           return p.name == port_name;
                         });
    }

    if (it == child_ports.end()) {
      diag_.Warning(item->loc, std::format("port '{}' not found on module '{}'",
                                           port_name, inst.module_name));
      binding.direction = Direction::kInput;
      binding.width = 1;
    } else {
      binding.direction = it->direction;
      binding.width = it->width;

      if (is_implicit && conn_expr &&
          IsNameDeclared(conn_expr->text, parent_mod)) {
        uint32_t sig_width = FindSignalWidth(conn_expr->text, parent_mod);
        if (sig_width != 0 && sig_width != it->width) {
          diag_.Error(
              item->loc,
              std::format("implicit named port connection '.{}' requires "
                          "equivalent data types (port width {}, "
                          "signal width {})",
                          port_name, it->width, sig_width));
        }

        NetType pnet = PortNetType(it->type_kind);
        if (pnet != NetType::kNone) {
          NetType snet = FindSignalNetType(conn_expr->text, parent_mod);
          if (snet != NetType::kNone && snet != pnet &&
              snet != NetType::kInterconnect && !it->is_interconnect) {
            diag_.Error(
                item->loc,
                std::format("implicit named port connection '.{}' between "
                            "dissimilar net types",
                            port_name));
          }
        }
      }

      if (!is_implicit && conn_expr &&
          conn_expr->kind == ExprKind::kIdentifier) {
        NetType pnet = PortNetType(it->type_kind);
        if (pnet != NetType::kNone) {
          NetType snet = FindSignalNetType(conn_expr->text, parent_mod);
          if (snet != NetType::kNone && snet != pnet) {
            if (DissimilarNetTypeRequiresWarning(pnet, snet)) {
              diag_.Warning(
                  item->loc,
                  std::format("port '{}' connected between dissimilar "
                              "net types",
                              binding.port_name));
            }
          }
        }
      }
    }

    if (conn_expr && conn_expr->kind == ExprKind::kIdentifier &&
        it != child_ports.end() && !it->is_interface_port) {
      DataTypeKind port_kind = NormalizeForCompatibility(it->type_kind);
      if (port_kind != DataTypeKind::kImplicit) {
        DataTypeKind sig_kind = DataTypeKind::kImplicit;
        auto vt = var_types_.find(conn_expr->text);
        if (vt != var_types_.end()) {
          sig_kind = NormalizeForCompatibility(vt->second);
        } else if (net_names_.count(conn_expr->text)) {
          sig_kind = DataTypeKind::kLogic;
        }
        if (sig_kind != DataTypeKind::kImplicit) {
          DataType port_dt{};
          port_dt.kind = port_kind;
          DataType sig_dt{};
          sig_dt.kind = sig_kind;
          if (!IsAssignmentCompatible(sig_dt, port_dt)) {
            diag_.Error(
                item->loc,
                std::format("port connection type is not assignment "
                            "compatible with port '{}'",
                            binding.port_name));
          }
        }
      }

      if (it->direction == Direction::kInout &&
          nettype_net_names_.count(conn_expr->text)) {
        diag_.Error(
            item->loc,
            std::format("user-defined nettype signal '{}' cannot connect "
                        "to inout port '{}'",
                        conn_expr->text, binding.port_name));
      }

      if (it->direction == Direction::kInout &&
          var_types_.count(conn_expr->text) &&
          net_names_.count(conn_expr->text) == 0) {
        diag_.Error(
            item->loc,
            std::format("variable '{}' cannot be connected to "
                        "inout port '{}'",
                        conn_expr->text, binding.port_name));
      }

      if (it->direction == Direction::kRef &&
          net_names_.count(conn_expr->text)) {
        diag_.Error(
            item->loc,
            std::format("net '{}' cannot be connected to ref port "
                        "'{}'; ref port requires a variable",
                        conn_expr->text, binding.port_name));
      }

      if (it->is_var && interconnect_names_.count(conn_expr->text)) {
        diag_.Error(
            item->loc,
            std::format("port variable '{}' cannot be connected to "
                        "interconnect net '{}'",
                        binding.port_name, conn_expr->text));
      }
    }

    // §11.4.12.1: Replication shall not appear on output/inout port connections.
    if (conn_expr && binding.direction != Direction::kInput) {
      std::function<bool(const Expr*)> has_rep = [&](const Expr* e) -> bool {
        if (!e) return false;
        if (e->kind == ExprKind::kReplicate) return true;
        if (e->kind == ExprKind::kConcatenation) {
          for (const auto* el : e->elements)
            if (has_rep(el)) return true;
        }
        return false;
      };
      if (has_rep(conn_expr)) {
        diag_.Error(conn_expr->range.start,
                    "replication shall not appear in an output or inout "
                    "port connection");
      }
    }

    // §10.9: Assignment pattern expressions shall not be used in port
    // expressions.
    if (conn_expr) {
      bool is_pattern = conn_expr->kind == ExprKind::kAssignmentPattern ||
                        (conn_expr->kind == ExprKind::kCast && conn_expr->lhs &&
                         conn_expr->lhs->kind == ExprKind::kAssignmentPattern);
      if (is_pattern) {
        diag_.Error(conn_expr->range.start,
                    "assignment pattern expression shall not be used in a "
                    "port expression");
      }
    }

    // §10.3.2: Track variables driven by module output ports.
    if (conn_expr && conn_expr->kind == ExprKind::kIdentifier &&
        binding.direction != Direction::kInput &&
        net_names_.count(conn_expr->text) == 0) {
      auto name = conn_expr->text;
      if (!output_port_targets_.emplace(name, item->loc).second) {
        diag_.Error(item->loc,
                    std::format("variable '{}' driven by multiple outputs",
                                name));
      }
    }

    if (is_ordered && !binding.connection &&
        binding.direction == Direction::kInput && it != child_ports.end() &&
        it->default_value) {
      binding.connection = it->default_value;
    }

    // §22.9: Pull unconnected input ports.
    if (has_pull && !binding.connection &&
        binding.direction == Direction::kInput) {
      binding.connection = MakePullExpr(unit_->unconnected_drive);
    }

    if (!binding.connection && binding.direction == Direction::kInput &&
        it != child_ports.end() && !it->is_var &&
        PortNetType(it->type_kind) != NetType::kNone) {
      binding.connection = MakeHighZExpr();
    }

    inst.port_bindings.push_back(binding);
  }

  if (item->inst_wildcard) {
    for (const auto& port : child_ports) {
      bool connected = false;
      for (const auto& [pname, _] : item->inst_ports) {
        if (pname == port.name) {
          connected = true;
          break;
        }
      }
      if (connected) continue;

      RtlirPortBinding binding;
      binding.port_name = port.name;
      binding.direction = port.direction;
      binding.width = port.width;

      if (port.is_interface_port) {
        if (port.interface_type_name.empty()) {
          diag_.Error(
              item->loc,
              std::format("implicit .* port connection cannot reference "
                          "generic interface port '{}' of module '{}'",
                          port.name, inst.module_name));
        } else if (interface_inst_types_.count(port.name)) {
          auto* expr = arena_.Create<Expr>();
          expr->kind = ExprKind::kIdentifier;
          expr->text = port.name;
          binding.connection = expr;
        }
      } else if (IsNameDeclared(port.name, parent_mod)) {
        uint32_t sig_width = FindSignalWidth(port.name, parent_mod);
        if (sig_width != 0 && sig_width != port.width) {
          diag_.Error(
              item->loc,
              std::format("implicit .* port connection '.{}' requires "
                          "equivalent data types (port width {}, "
                          "signal width {})",
                          port.name, port.width, sig_width));
        }

        NetType pnet = PortNetType(port.type_kind);
        if (pnet != NetType::kNone) {
          NetType snet = FindSignalNetType(port.name, parent_mod);
          if (snet != NetType::kNone && snet != pnet &&
              snet != NetType::kInterconnect && !port.is_interconnect) {
            diag_.Error(
                item->loc,
                std::format("implicit .* port connection '.{}' between "
                            "dissimilar net types",
                            port.name));
          }
        }

        if (port.direction == Direction::kInout &&
            nettype_net_names_.count(port.name)) {
          diag_.Error(
              item->loc,
              std::format("user-defined nettype signal '{}' cannot connect "
                          "to inout port '{}'",
                          port.name, port.name));
        }

        if (port.direction == Direction::kInout &&
            var_types_.count(port.name) &&
            net_names_.count(port.name) == 0) {
          diag_.Error(
              item->loc,
              std::format("variable '{}' cannot be connected to "
                          "inout port '{}'",
                          port.name, port.name));
        }

        if (port.direction == Direction::kRef &&
            net_names_.count(port.name)) {
          diag_.Error(
              item->loc,
              std::format("net '{}' cannot be connected to ref port "
                          "'{}'; ref port requires a variable",
                          port.name, port.name));
        }

        if (port.is_var && interconnect_names_.count(port.name)) {
          diag_.Error(
              item->loc,
              std::format("port variable '{}' cannot be connected to "
                          "interconnect net '{}'",
                          port.name, port.name));
        }

        auto* expr = arena_.Create<Expr>();
        expr->kind = ExprKind::kIdentifier;
        expr->text = port.name;
        binding.connection = expr;

        if (binding.direction != Direction::kInput &&
            net_names_.count(port.name) == 0) {
          if (!output_port_targets_.emplace(port.name, item->loc).second) {
            diag_.Error(
                item->loc,
                std::format("variable '{}' driven by multiple outputs",
                            port.name));
          }
        }
      } else if (port.default_value) {
        binding.connection = port.default_value;
      } else if (has_pull && port.direction == Direction::kInput) {
        binding.connection = MakePullExpr(unit_->unconnected_drive);
      } else if (port.direction == Direction::kInput && !port.is_var &&
                 PortNetType(port.type_kind) != NetType::kNone) {
        binding.connection = MakeHighZExpr();
      }

      if (binding.connection) {
        inst.port_bindings.push_back(binding);
      }
    }
  } else {
    size_t first_unconnected = is_ordered ? item->inst_ports.size() : 0;
    for (size_t i = first_unconnected; i < child_ports.size(); ++i) {
      const auto& port = child_ports[i];
      if (port.direction != Direction::kInput) continue;

      if (!is_ordered) {
        bool connected = false;
        for (const auto& [pname, _] : item->inst_ports) {
          if (pname == port.name) {
            connected = true;
            break;
          }
        }
        if (connected) continue;
      }

      RtlirPortBinding binding;
      binding.port_name = port.name;
      binding.direction = port.direction;
      binding.width = port.width;

      if (port.default_value) {
        binding.connection = port.default_value;
      } else if (has_pull) {
        binding.connection = MakePullExpr(unit_->unconnected_drive);
      } else if (!port.is_var &&
                 PortNetType(port.type_kind) != NetType::kNone) {
        binding.connection = MakeHighZExpr();
      }

      if (binding.connection) {
        inst.port_bindings.push_back(binding);
      }
    }
  }

  for (const auto& port : child_ports) {
    if (port.direction != Direction::kRef) continue;
    bool connected = false;
    for (const auto& binding : inst.port_bindings) {
      if (binding.port_name == port.name && binding.connection) {
        connected = true;
        break;
      }
    }
    if (!connected) {
      diag_.Error(item->loc,
                  std::format("ref port '{}' of module '{}' cannot be "
                              "left unconnected",
                              port.name, inst.module_name));
    }
  }

  for (const auto& port : child_ports) {
    if (!port.is_interface_port) continue;

    Expr* conn = nullptr;
    for (const auto& binding : inst.port_bindings) {
      if (binding.port_name == port.name) {
        conn = binding.connection;
        break;
      }
    }

    if (!conn) {
      diag_.Error(item->loc,
                  std::format("interface port '{}' of module '{}' cannot be "
                              "left unconnected",
                              port.name, inst.module_name));
      continue;
    }

    std::string_view conn_name;
    if (conn->kind == ExprKind::kIdentifier) {
      conn_name = conn->text;
    } else if (conn->kind == ExprKind::kMemberAccess && conn->lhs &&
               conn->lhs->kind == ExprKind::kIdentifier && conn->rhs &&
               conn->rhs->kind == ExprKind::kIdentifier) {
      conn_name = conn->lhs->text;
    } else {
      diag_.Error(item->loc,
                  std::format("interface port '{}' must be connected to an "
                              "interface instance or interface port",
                              port.name));
      continue;
    }

    std::string_view conn_ifc_type;

    auto iit = interface_inst_types_.find(conn_name);
    if (iit != interface_inst_types_.end()) {
      conn_ifc_type = iit->second;
    } else {
      bool is_ifc_port = false;
      for (const auto& pp : parent_mod->ports) {
        if (pp.name == conn_name && pp.is_interface_port) {
          conn_ifc_type = pp.interface_type_name;
          is_ifc_port = true;
          break;
        }
      }
      if (!is_ifc_port) {
        diag_.Error(
            item->loc,
            std::format("interface port '{}' must be connected to an "
                        "interface instance or interface port",
                        port.name));
        continue;
      }
    }

    if (!port.interface_type_name.empty() && !conn_ifc_type.empty() &&
        port.interface_type_name != conn_ifc_type) {
      diag_.Error(
          item->loc,
          std::format("interface port '{}' requires interface type '{}' "
                      "but is connected to instance of type '{}'",
                      port.name, port.interface_type_name, conn_ifc_type));
    }
  }
}

void Elaborator::CheckPortCoercion(const RtlirModuleInst& inst, SourceLoc loc) {
  if (!inst.resolved) return;

  std::unordered_set<std::string_view> child_assign_targets;
  for (const auto& ca : inst.resolved->assigns) {
    if (ca.lhs && ca.lhs->kind == ExprKind::kIdentifier)
      child_assign_targets.insert(ca.lhs->text);
  }

  for (const auto& binding : inst.port_bindings) {
    if (binding.direction == Direction::kInput &&
        child_assign_targets.count(binding.port_name)) {
      diag_.Warning(
          loc, std::format("port '{}' is declared as input but is driven "
                           "inside module '{}'",
                           binding.port_name, inst.module_name));
    }

    if (binding.direction == Direction::kOutput && binding.connection &&
        binding.connection->kind == ExprKind::kIdentifier &&
        cont_assign_targets_.count(binding.connection->text)) {
      diag_.Warning(
          loc,
          std::format("port '{}' is declared as output but its connection "
                      "'{}' is also driven externally",
                      binding.port_name, binding.connection->text));
    }
  }
}

void Elaborator::CheckUwirePortMerge(const RtlirModuleInst& inst,
                                     const ModuleItem* item,
                                     RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    if (!binding.connection) continue;

    auto port_it = std::find_if(
        child_ports.begin(), child_ports.end(),
        [&](const RtlirPort& p) { return p.name == binding.port_name; });
    if (port_it == child_ports.end()) continue;

    NetType internal_net = PortNetType(port_it->type_kind);
    bool internal_is_uwire = (internal_net == NetType::kUwire);

    bool external_is_net = false;
    bool external_is_uwire = false;
    if (binding.connection->kind == ExprKind::kIdentifier) {
      NetType ext = FindSignalNetType(binding.connection->text, parent_mod);
      external_is_net = (ext != NetType::kNone);
      external_is_uwire = (ext == NetType::kUwire);
    }

    if (!internal_is_uwire && !external_is_uwire) continue;

    bool merged = (internal_net != NetType::kNone) && external_is_net;
    if (!merged) {
      diag_.Warning(
          item->loc,
          std::format("uwire net on port '{}' of instance '{}' is not "
                      "merged into a single net",
                      binding.port_name, inst.inst_name));
    }
  }
}

void Elaborator::CheckInterconnectPortMerge(const RtlirModuleInst& inst,
                                            const ModuleItem* item,
                                            RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    if (!binding.connection) continue;

    auto port_it = std::find_if(
        child_ports.begin(), child_ports.end(),
        [&](const RtlirPort& p) { return p.name == binding.port_name; });
    if (port_it == child_ports.end()) continue;

    bool internal_is_interconnect = port_it->is_interconnect;

    bool external_is_interconnect = false;
    if (binding.connection->kind == ExprKind::kIdentifier) {
      external_is_interconnect =
          interconnect_names_.count(binding.connection->text) != 0;
    }

    if (internal_is_interconnect && external_is_interconnect) {
      diag_.Error(
          item->loc,
          std::format("simulated net for port '{}' of instance '{}' has "
                      "interconnect type at end of elaboration",
                      binding.port_name, inst.inst_name));
    }
  }
}

void Elaborator::ResolveInterconnectPrimitiveTerminals(
    const std::vector<Expr*>& terminals, RtlirModule* mod) {
  for (const auto* term : terminals) {
    if (!term || term->kind != ExprKind::kIdentifier) continue;
    if (interconnect_names_.count(term->text) == 0) continue;
    auto scoped = ScopedName(term->text);
    for (auto& net : mod->nets) {
      if (net.name == scoped && net.net_type == NetType::kInterconnect) {
        net.net_type = NetType::kWire;
        break;
      }
    }
    interconnect_names_.erase(term->text);
  }
}

void Elaborator::ValidateUnpackedArrayPorts(const RtlirModuleInst& inst,
                                            const ModuleItem* item,
                                            RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    auto port_it = std::find_if(
        child_ports.begin(), child_ports.end(),
        [&](const RtlirPort& p) { return p.name == binding.port_name; });
    if (port_it == child_ports.end()) continue;
    if (port_it->num_unpacked_dims == 0) continue;

    if (!binding.connection ||
        binding.connection->kind != ExprKind::kIdentifier) {
      diag_.Error(item->loc,
                  std::format("unpacked array port '{}' requires a matching "
                              "unpacked array connection",
                              binding.port_name));
      continue;
    }

    auto it = var_array_info_.find(binding.connection->text);
    if (it == var_array_info_.end()) {
      diag_.Error(item->loc,
                  std::format("unpacked array port '{}' requires a matching "
                              "unpacked array connection",
                              binding.port_name));
      continue;
    }

    const auto& conn_info = it->second;
    if (conn_info.num_unpacked_dims != port_it->num_unpacked_dims) {
      diag_.Error(
          item->loc,
          std::format("unpacked array port '{}' has {} unpacked dimension(s) "
                      "but connection has {}",
                      binding.port_name, port_it->num_unpacked_dims,
                      conn_info.num_unpacked_dims));
      continue;
    }

    for (uint32_t d = 0; d < port_it->num_unpacked_dims; ++d) {
      if (d < port_it->unpacked_dim_sizes.size() &&
          d < conn_info.dim_sizes.size() &&
          port_it->unpacked_dim_sizes[d] != conn_info.dim_sizes[d]) {
        diag_.Error(
            item->loc,
            std::format("unpacked array port '{}' dimension {} has size {} "
                        "but connection has size {}",
                        binding.port_name, d, port_it->unpacked_dim_sizes[d],
                        conn_info.dim_sizes[d]));
        break;
      }
    }
  }
}

void Elaborator::ValidateInstanceArrayPorts(
    const RtlirModuleInst& inst, const ModuleItem* item,
    RtlirModule* parent_mod, const std::vector<uint32_t>& inst_dim_sizes,
    uint32_t total_instances) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& binding : inst.port_bindings) {
    if (!binding.connection) continue;

    auto port_it = std::find_if(
        child_ports.begin(), child_ports.end(),
        [&](const RtlirPort& p) { return p.name == binding.port_name; });
    if (port_it == child_ports.end()) continue;

    bool conn_is_unpacked = false;
    uint32_t conn_num_dims = 0;
    const std::vector<uint32_t>* conn_dim_sizes_ptr = nullptr;
    uint32_t conn_width = 0;

    if (binding.connection->kind == ExprKind::kIdentifier) {
      auto it = var_array_info_.find(binding.connection->text);
      if (it != var_array_info_.end()) {
        conn_is_unpacked = true;
        conn_num_dims = it->second.num_unpacked_dims;
        conn_dim_sizes_ptr = &it->second.dim_sizes;
      }
      conn_width = FindSignalWidth(binding.connection->text, parent_mod);
    }

    if (conn_is_unpacked) {
      uint32_t expected_dims =
          static_cast<uint32_t>(inst_dim_sizes.size()) +
          port_it->num_unpacked_dims;
      if (conn_num_dims != expected_dims) {
        diag_.Error(
            item->loc,
            std::format("unpacked array connection to port '{}' has {} "
                        "dimension(s) but expected {}",
                        binding.port_name, conn_num_dims, expected_dims));
        continue;
      }
      if (conn_dim_sizes_ptr) {
        for (size_t d = 0; d < inst_dim_sizes.size(); ++d) {
          if (d < conn_dim_sizes_ptr->size() &&
              (*conn_dim_sizes_ptr)[d] != inst_dim_sizes[d]) {
            diag_.Error(
                item->loc,
                std::format("unpacked array connection to port '{}' "
                            "dimension {} has size {} but instance array "
                            "has size {}",
                            binding.port_name, d, (*conn_dim_sizes_ptr)[d],
                            inst_dim_sizes[d]));
            break;
          }
        }
        for (uint32_t d = 0; d < port_it->num_unpacked_dims; ++d) {
          uint32_t ci = static_cast<uint32_t>(inst_dim_sizes.size()) + d;
          if (ci < conn_dim_sizes_ptr->size() &&
              d < port_it->unpacked_dim_sizes.size() &&
              (*conn_dim_sizes_ptr)[ci] != port_it->unpacked_dim_sizes[d]) {
            diag_.Error(
                item->loc,
                std::format("unpacked array connection to port '{}' "
                            "port dimension {} has size {} but port "
                            "expects {}",
                            binding.port_name, d, (*conn_dim_sizes_ptr)[ci],
                            port_it->unpacked_dim_sizes[d]));
            break;
          }
        }
      }
    } else if (conn_width != 0 && conn_width != port_it->width) {
      uint32_t expected_width = port_it->width * total_instances;
      if (conn_width != expected_width) {
        diag_.Error(
            item->loc,
            std::format("packed array connection to port '{}' has width {} "
                        "but expected {} ({} instances * port width {})",
                        binding.port_name, conn_width, expected_width,
                        total_instances, port_it->width));
      }
    }
  }
}

// --- Generate expansion ---

ScopeMap Elaborator::BuildParamScope(const RtlirModule* mod) const {
  ScopeMap scope = cu_param_scope_;
  for (const auto& p : mod->params) {
    if (p.is_resolved) {
      scope[p.name] = p.resolved_value;
    }
  }
  return scope;
}

void Elaborator::ProcessPendingGenerate(ModuleItem* item, RtlirModule* mod) {
  auto scope = BuildParamScope(mod);
  switch (item->kind) {
    case ModuleItemKind::kGenerateIf:
      ElaborateGenerateIf(item, mod, scope);
      break;
    case ModuleItemKind::kGenerateCase:
      ElaborateGenerateCase(item, mod, scope);
      break;
    case ModuleItemKind::kGenerateFor:
      ElaborateGenerateFor(item, mod, scope);
      break;
    default:
      break;
  }
}

void Elaborator::ElaborateGenerateItems(const std::vector<ModuleItem*>& items,
                                        RtlirModule* mod,
                                        const ScopeMap& scope) {
  for (auto* item : items) {
    switch (item->kind) {
      case ModuleItemKind::kGenerateIf:
        ElaborateGenerateIf(item, mod, scope);
        break;
      case ModuleItemKind::kGenerateCase:
        ElaborateGenerateCase(item, mod, scope);
        break;
      case ModuleItemKind::kGenerateFor:
        ElaborateGenerateFor(item, mod, scope);
        break;
      default:
        ElaborateItem(item, mod);
        break;
    }
  }
}

void Elaborator::ElaborateGenerateIf(ModuleItem* item, RtlirModule* mod,
                                     const ScopeMap& scope) {
  auto cond = ConstEvalInt(item->gen_cond, scope);
  if (!cond) {
    diag_.Warning(item->loc, "generate-if condition is not constant");
    return;
  }
  if (*cond) {
    ElaborateGenerateItems(item->gen_body, mod, scope);
  } else if (item->gen_else) {
    ElaborateGenerateItems(item->gen_else->gen_body, mod, scope);
  }
}

static bool MatchesCasePattern(const std::vector<Expr*>& patterns,
                               int64_t selector, const ScopeMap& scope) {
  for (const auto* pat : patterns) {
    auto val = ConstEvalInt(pat, scope);
    if (val && *val == selector) return true;
  }
  return false;
}

void Elaborator::ElaborateGenerateCase(ModuleItem* item, RtlirModule* mod,
                                       const ScopeMap& scope) {
  auto selector = ConstEvalInt(item->gen_cond, scope);
  if (!selector) {
    diag_.Warning(item->loc, "generate-case selector is not constant");
    return;
  }
  const std::vector<ModuleItem*>* default_body = nullptr;
  for (const auto& ci : item->gen_case_items) {
    if (ci.is_default) {
      default_body = &ci.body;
      continue;
    }
    if (MatchesCasePattern(ci.patterns, *selector, scope)) {
      ElaborateGenerateItems(ci.body, mod, scope);
      return;
    }
  }
  if (default_body) {
    ElaborateGenerateItems(*default_body, mod, scope);
  }
}

std::string_view Elaborator::ScopedName(std::string_view base) {
  if (gen_prefix_.empty()) return base;
  std::string full = gen_prefix_ + std::string(base);
  return {arena_.AllocString(full.c_str(), full.size()), full.size()};
}

static constexpr int64_t kMaxGenerateIterations = 65536;

void Elaborator::ElaborateGenerateFor(ModuleItem* item, RtlirModule* mod,
                                      const ScopeMap& scope) {
  if (!item->gen_init || !item->gen_init->lhs) {
    diag_.Warning(item->loc, "malformed generate-for initializer");
    return;
  }
  auto genvar_name = item->gen_init->lhs->text;
  auto init_val = ConstEvalInt(item->gen_init->rhs, scope);
  if (!init_val) {
    diag_.Warning(item->loc, "generate-for init is not constant");
    return;
  }

  ScopeMap loop_scope = scope;
  loop_scope[genvar_name] = *init_val;
  std::string saved_prefix = gen_prefix_;

  for (int64_t iter = 0; iter < kMaxGenerateIterations; ++iter) {
    auto cond = ConstEvalInt(item->gen_cond, loop_scope);
    if (!cond || !*cond) break;

    gen_prefix_ = std::format("{}{}_{}_", saved_prefix, genvar_name,
                              loop_scope[genvar_name]);
    ElaborateGenerateItems(item->gen_body, mod, loop_scope);

    // Evaluate genvar_iteration step: supports i = expr, i += expr,
    // ++i, i++, --i, i-- (§A.4.2 genvar_iteration).
    std::optional<int64_t> next;
    if (item->gen_step->rhs) {
      next = ConstEvalInt(item->gen_step->rhs, loop_scope);
    } else if (item->gen_step->expr) {
      auto* e = item->gen_step->expr;
      if ((e->kind == ExprKind::kUnary ||
           e->kind == ExprKind::kPostfixUnary) &&
          e->lhs && e->lhs->kind == ExprKind::kIdentifier) {
        auto it = loop_scope.find(e->lhs->text);
        if (it != loop_scope.end()) {
          if (e->op == TokenKind::kPlusPlus)
            next = it->second + 1;
          else if (e->op == TokenKind::kMinusMinus)
            next = it->second - 1;
        }
      }
    }
    if (!next) break;
    loop_scope[genvar_name] = *next;
  }

  gen_prefix_ = saved_prefix;
}

}  // namespace delta
