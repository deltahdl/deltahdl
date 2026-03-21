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
  var.width = 32;
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
  if (item->data_type.kind == DataTypeKind::kVoid &&
      item->typedef_type.kind != DataTypeKind::kImplicit) {
    typedefs_[item->name] = item->typedef_type;
  }
  RtlirParamDecl pd;
  pd.name = item->name;
  pd.is_localparam = item->is_localparam;
  pd.default_value = item->init_expr;
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
      AddProcess(MapAlwaysKind(item->always_kind), item, mod, arena_, diag_);
      break;
    case ModuleItemKind::kModuleInst:
      ElaborateModuleInst(item, mod);
      break;
    case ModuleItemKind::kParamDecl:
      ElaborateParamDecl(item, mod);
      break;
    case ModuleItemKind::kGenerateIf:
      ElaborateGenerateIf(item, mod, BuildParamScope(mod));
      break;
    case ModuleItemKind::kGenerateCase:
      ElaborateGenerateCase(item, mod, BuildParamScope(mod));
      break;
    case ModuleItemKind::kGenerateFor:
      ElaborateGenerateFor(item, mod, BuildParamScope(mod));
      break;
    case ModuleItemKind::kTypedef:
      ElaborateTypedef(item, mod);
      break;
    case ModuleItemKind::kNettypeDecl:
      ElaborateNettypeDecl(item, mod);
      break;
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kTaskDecl:
      ValidateFunctionBody(item);
      mod->function_decls.push_back(item);
      break;
    case ModuleItemKind::kGateInst:
      ElaborateGateInst(item, mod, arena_);
      break;
    case ModuleItemKind::kUdpInst:
      break;
    case ModuleItemKind::kSpecparam:
      specparam_names_.insert(item->name);
      ElaborateSpecparam(item, mod);
      break;
    case ModuleItemKind::kAlias: {
      ValidateAlias(item);
      RtlirAlias alias;
      alias.nets = item->alias_nets;
      mod->aliases.push_back(alias);
      break;
    }
    case ModuleItemKind::kDefparam:
    case ModuleItemKind::kImportDecl:
    case ModuleItemKind::kExportDecl:
    case ModuleItemKind::kPropertyDecl:
    case ModuleItemKind::kSequenceDecl:
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
    case ModuleItemKind::kClassDecl:
      if (item->class_decl) {
        class_names_.insert(item->class_decl->name);
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
    ValidateVoidMembers(item->typedef_type, item->loc);
    ValidateRandQualifiers(item->typedef_type, item->loc);
    ValidatePackedStructMemberTypes(item->typedef_type, item->loc);
    ValidateChandleInUnion(item->typedef_type, item->loc);
    ValidatePackedUnion(item->typedef_type, item->loc);
  }
  ValidatePackedDimOnPredefinedType(item->typedef_type, item->loc);
  if (item->typedef_type.kind != DataTypeKind::kEnum) return;
  ValidateEnumDecl(item->typedef_type, item->loc);
  int64_t next_val = 0;
  std::vector<RtlirEnumMember> members;
  for (const auto& member : item->typedef_type.enum_members) {
    enum_member_names_.insert(member.name);
    if (member.value) {
      next_val = ConstEvalInt(member.value).value_or(next_val);
    }
    members.push_back({member.name, next_val});
    RtlirVariable var;
    var.name = member.name;
    var.width = EvalTypeWidth(item->typedef_type, typedefs_);
    var.is_4state = false;
    mod->variables.push_back(var);
    ++next_val;
  }
  mod->enum_types[item->name] = std::move(members);
}

// §6.6.7: Register a user-defined nettype so declarations using it create nets.
void Elaborator::ElaborateNettypeDecl(ModuleItem* item, RtlirModule* /*mod*/) {
  typedefs_[item->name] = item->typedef_type;
  nettype_names_.insert(item->name);
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
  nettype_net_names_.clear();
  interconnect_names_.clear();
  var_named_types_.clear();
  clocking_signals_.clear();
  task_names_.clear();
  func_decls_.clear();
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
  for (auto* item : decl->items) {
    ElaborateItem(item, mod);
  }
  // §9.2.2.2: Check for multi-driver violations on always_comb LHS variables.
  CheckAlwaysCombMultiDriver(decl, mod);
  ValidateModuleConstraints(decl);
  ValidateClockvarAccess(decl);
  ValidateCycleDelayDefaultClocking(decl);
  ValidateDuplicateDefaultClocking(decl);
  ValidateDuplicateGlobalClocking(decl);
  ValidateContAssignToClockvar(decl);
  ValidateConstantFunctionCalls(decl);
}

// --- Module instantiation ---

void Elaborator::ElaborateModuleInst(ModuleItem* item, RtlirModule* mod) {
  RtlirModuleInst inst;
  inst.module_name = item->inst_module;
  inst.inst_name = item->inst_name;

  auto* child_decl = FindModule(item->inst_module);
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

  ParamList child_params;
  inst.resolved = ElaborateModule(child_decl, child_params);
  BindPorts(inst, item, mod);
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

void Elaborator::BindPorts(RtlirModuleInst& inst, const ModuleItem* item,
                           RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;
  const bool has_pull = unit_->unconnected_drive != NetType::kWire;

  for (auto& [port_name, conn_expr] : item->inst_ports) {
    // §6.10: Create implicit nets for undeclared identifiers in connections.
    if (conn_expr && conn_expr->kind == ExprKind::kIdentifier) {
      MaybeCreateImplicitNet(conn_expr->text, item->loc, parent_mod);
    }
    RtlirPortBinding binding;
    binding.port_name = port_name;
    binding.connection = conn_expr;

    auto it =
        std::find_if(child_ports.begin(), child_ports.end(),
                     [&](const RtlirPort& p) { return p.name == port_name; });
    if (it == child_ports.end()) {
      diag_.Warning(item->loc, std::format("port '{}' not found on module '{}'",
                                           port_name, inst.module_name));
      binding.direction = Direction::kInput;
      binding.width = 1;
    } else {
      binding.direction = it->direction;
      binding.width = it->width;
    }

    // §22.9: Pull unconnected input ports.
    if (has_pull && !binding.connection &&
        binding.direction == Direction::kInput) {
      binding.connection = MakePullExpr(unit_->unconnected_drive);
    }

    inst.port_bindings.push_back(binding);
  }

  // §22.9: Add pull bindings for input ports not mentioned in the connection.
  if (has_pull) {
    for (const auto& port : child_ports) {
      if (port.direction != Direction::kInput) continue;
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
      binding.connection = MakePullExpr(unit_->unconnected_drive);
      inst.port_bindings.push_back(binding);
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
