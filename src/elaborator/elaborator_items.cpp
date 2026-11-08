#include <cstdint>
#include <format>
#include <functional>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/assertion_rules.h"
#include "elaborator/checker_actual_rules.h"
#include "elaborator/checker_instance_binding.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/elaborator_node_attributes.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/implication_operator_rules.h"
#include "elaborator/interconnect_uses.h"
#include "elaborator/procedural_checker_instance.h"
#include "elaborator/procedural_concurrent_assertion.h"
#include "elaborator/property_instance.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_alias.h"
#include "elaborator/rtlir_checker_site.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/sensitivity.h"
#include "elaborator/subroutine_instance_copy.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_param_scope_prefix.h"
#include "elaborator/type_ref_compare_fold.h"
#include "elaborator/type_ref_walks.h"
#include "elaborator/unit_scope_order.h"
#include "elaborator/uwire_drivers.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/override_specifier_placement.h"

namespace delta {

uint32_t SpecparamWidth(const DataType& type, const Expr* init,
                        const TypedefMap& typedefs) {
  if (type.packed_dim_left != nullptr && type.packed_dim_right != nullptr) {
    uint32_t w = EvalTypeWidth(type);
    return w == 0 ? 32 : w;
  }
  if (init != nullptr) {
    uint32_t w = InferExprWidth(init, typedefs);
    return w == 0 ? 32 : w;
  }
  return 32;
}

bool SpecparamIsReal(const DataType& type, const Expr* init) {
  if (type.packed_dim_left != nullptr && type.packed_dim_right != nullptr) {
    return false;
  }
  return HasRealOperand(init);
}

void Elaborator::ElaborateSpecparam(ModuleItem* item, RtlirModule* mod) {
  RtlirVariable var;
  var.name = ScopedName(item->name);
  var.loc = item->loc;
  var.width = SpecparamWidth(item->data_type, item->init_expr, typedefs_);
  var.is_real = SpecparamIsReal(item->data_type, item->init_expr);
  if (var.is_real) var.width = 64;
  var.init_expr = item->init_expr;
  var.attrs = ResolveAttributes(item->attrs, diag_, BuildParamScope(mod));
  mod->variables.push_back(var);
  mod->specparam_names.push_back(var.name);
}

bool PortSelectsFrom(const RtlirPort& port, std::string_view name) {
  if (port.selected_width == 0) return false;
  const Expr* root = port.port_expr;
  while (root != nullptr && root->kind == ExprKind::kSelect) root = root->base;
  return root != nullptr && root->kind == ExprKind::kIdentifier &&
         root->text == name;
}

bool IsNameDeclared(std::string_view name, const RtlirModule* mod) {
  for (const auto& v : mod->variables) {
    if (v.name == name) return true;
  }
  for (const auto& n : mod->nets) {
    if (n.name == name) return true;
  }
  for (const auto& p : mod->ports) {
    if (p.name == name || PortSelectsFrom(p, name)) return true;
  }
  return false;
}

static bool IsParamDeclared(std::string_view name, const RtlirModule* mod,
                            const std::vector<std::string_view>& scopes) {
  for (const auto& p : mod->params) {
    if (p.name != name) continue;
    if (ParamVisibleFromScopes(p.gen_block_prefix, scopes)) return true;
  }
  return false;
}

bool Elaborator::MaybeCreateImplicitNet(std::string_view name, SourceLoc loc,
                                        RtlirModule* mod) {
  for (auto it = gen_prefix_scopes_.rbegin(); it != gen_prefix_scopes_.rend();
       ++it) {
    if (IsNameDeclared(std::string(*it) + std::string(name), mod)) return true;
  }
  if (IsNameDeclared(name, mod)) return true;
  if (IsParamDeclared(name, mod, gen_prefix_scopes_)) return true;
  if (UnitDeclaresData(unit_, name, loc)) return true;
  if (mod->default_nettype == NetType::kNone) {
    diag_.Error(loc,
                std::format("implicit net '{}' forbidden by "
                            "`default_nettype none",
                            name),
                Subclause("22.8"));
    return false;
  }
  std::string_view scoped = ScopedName(name);
  RtlirNet net = MakeImplicitPortNet(scoped, 1, false, mod->default_nettype);
  net.refers_outward = IsNameInEnclosingScope(name);
  net.implicit_ref_loc = loc;
  mod->nets.push_back(net);
  declared_names_.insert(scoped);
  net_names_.insert(name);
  if (net.net_type == NetType::kUwire) uwire_drivers_.Declare(scoped);
  return true;
}

void Elaborator::ValidateTypenameAsElabConstant(const Expr* init) {
  if (init->kind != ExprKind::kSystemCall) return;
  if (init->callee != "$typename") return;
  if (init->args.empty()) return;
  const auto* arg = init->args[0];
  if (arg->kind == ExprKind::kMemberAccess) {
    diag_.Error(arg->range.start,
                "$typename cannot serve as an elaboration-time constant when "
                "its argument is a hierarchical reference",
                Subclause("20.6.1"));
    return;
  }
  if (arg->kind != ExprKind::kSelect) return;
  auto it = var_array_info_.find(arg->base->text);
  if (it == var_array_info_.end()) return;
  if (!it->second.is_dynamic && !it->second.is_assoc) return;
  diag_.Error(arg->range.start,
              "$typename cannot serve as an elaboration-time constant when its "
              "argument selects an element of a dynamic object",
              Subclause("20.6.1"));
}

namespace {

void CheckGateInstanceArrayTerminalWidths(
    const ModuleItem* item, const RtlirModule* mod, const ScopeMap& scope,
    const std::unordered_set<std::string_view>& interconnect_names,
    DiagEngine& diag) {
  auto len = InstanceArrayLength(item, scope);
  if (!len) {
    diag.Error(item->loc,
               "gate, switch or primitive instance range bound is not a "
               "constant expression",
               Subclause("28.3.5"));
    return;
  }
  uint32_t array_len = *len;
  for (auto* term : item->gate_terminals) {
    uint32_t w = GateTerminalWidth(term, mod, scope);
    if (w == 0) continue;
    bool is_interconnect = term && term->kind == ExprKind::kIdentifier &&
                           interconnect_names.count(term->text) != 0;
    if (is_interconnect) {
      if (w != array_len) {
        diag.Error(item->loc,
                   "interconnect terminal of a gate or primitive instance "
                   "array must have a bit-length equal to the instance-array "
                   "length",
                   Subclause("28.3.6"));
        break;
      }
      continue;
    }
    if (w != 1 && w != array_len) {
      diag.Error(item->loc,
                 "gate or primitive array terminal width does not match "
                 "either the per-instance port width or the instance-array "
                 "length",
                 Subclause("28.3.6"));
      break;
    }
  }
}

void CheckGateInstNameDiagnostics(const ModuleItem* item, DiagEngine& diag) {
  if (!item->gate_inst_name.empty() && !item->gate_terminals.empty() &&
      item->gate_terminals[0] &&
      item->gate_terminals[0]->kind == ExprKind::kIdentifier &&
      item->gate_terminals[0]->text == item->gate_inst_name) {
    diag.Error(item->loc,
               std::format("gate instance name '{}' conflicts with its "
                           "output net",
                           item->gate_inst_name),
               Subclause("23.9"));
  }
}

void RecordImportDecl(const ModuleItem* item, RtlirModule* mod) {
  RtlirImport imp;
  imp.package_name = item->import_item.package_name;
  imp.item_name = item->import_item.item_name;
  imp.is_wildcard = item->import_item.is_wildcard;
  mod->imports.push_back(imp);
}

void RecordClassDecl(
    const ModuleItem* item, RtlirModule* mod,
    std::unordered_set<std::string_view>& class_names,
    std::unordered_set<std::string_view>& parameterized_class_names) {
  if (!item->class_decl) return;
  class_names.insert(item->class_decl->name);
  if (!item->class_decl->params.empty()) {
    parameterized_class_names.insert(item->class_decl->name);
  }
  mod->class_decls.push_back(item->class_decl);
}

template <typename MakeNet>
void CreateImplicitNetsForTerminals(const std::vector<Expr*>& terminals,
                                    SourceLoc loc, MakeNet&& make_net) {
  for (auto* term : terminals) {
    if (term && term->kind == ExprKind::kIdentifier) {
      make_net(term->text, loc);
    }
  }
}

bool HasInstanceArrayRange(const ModuleItem* item) {
  return item->inst_range_left != nullptr && item->inst_range_right != nullptr;
}

std::string_view ModuleNameSpaceEntry(const ModuleItem* item) {
  switch (item->kind) {
    case ModuleItemKind::kParamDecl:
    case ModuleItemKind::kClassDecl:
    case ModuleItemKind::kLetDecl:
    case ModuleItemKind::kCovergroupDecl:
    case ModuleItemKind::kSequenceDecl:
    case ModuleItemKind::kPropertyDecl:
    case ModuleItemKind::kSpecparam:
      return item->name;
    case ModuleItemKind::kTypedef:
      return item->typedef_type.kind == DataTypeKind::kImplicit &&
                     item->typedef_type.type_ref_expr == nullptr
                 ? std::string_view{}
                 : item->name;
    case ModuleItemKind::kVarDecl:
      return item->is_genvar ? item->name : std::string_view{};
    case ModuleItemKind::kClockingBlock:
      return item->clocking_event.empty() ? std::string_view{} : item->name;
    case ModuleItemKind::kNestedModuleDecl:
      return item->nested_module_decl->is_extern
                 ? std::string_view{}
                 : item->nested_module_decl->name;
    default:
      return {};
  }
}

}  // namespace

void Elaborator::CheckPrimitiveTerminals(const ModuleItem* item,
                                         const RtlirModule* mod) {
  ScopeMap scope = BuildParamScope(mod);
  if (HasInstanceArrayRange(item)) {
    CheckGateInstanceArrayTerminalWidths(item, mod, scope, interconnect_names_,
                                         diag_);
  }
  ValidatePrimitiveOutputTerminalWidths(
      item, mod, scope, ScopedDeclarations{gen_prefix_scopes_, declared_names_},
      diag_);
  for (const auto& [name, value] : gen_const_scope_) scope[name] = value;
  ValidatePrimitiveDrivenTerminals(item, mod, scope, gen_prefix_scopes_, diag_);
  ReportInterconnectInInstance(*item, interconnect_names_, diag_);
  RecordUwirePrimitiveOutputs(uwire_drivers_, item,
                              {mod,
                               var_types_,
                               unit_,
                               unit_uwire_drivers_,
                               {gen_prefix_scopes_, declared_names_},
                               scope},
                              diag_);
}

static TypeRefCompareFolder RecordingInto(
    RtlirModule* mod, std::string_view gen_prefix,
    std::function<std::optional<int64_t>(const Expr*)> judge) {
  return [mod, gen_prefix, judge = std::move(judge)](const Expr* e) {
    std::optional<int64_t> holds = judge(e);
    if (holds.has_value()) {
      mod->type_ref_compares.push_back(
          {.expr = e, .gen_prefix = gen_prefix, .holds = *holds != 0});
    }
    return holds;
  };
}

void Elaborator::ElaborateItem(ModuleItem* item, RtlirModule* mod) {
  if (item->kind == ModuleItemKind::kBindDirective) {
    generate_binds_.insert(item->bind_directive);
    return;
  }
  if (ItemCarriesDelay(item)) {
    ValidateItemDelaysNonNegative(item, BuildParamScope(mod), diag_);
  }
  DeclareInModuleNameSpace(ModuleNameSpaceEntry(item), item->loc);
  RecordNodeAttributes(*item, *mod, diag_,
                       [&] { return BuildParamScope(mod); });
  ReportItemImplicationOperators(*item, diag_);
  const TypeRefCompareFolder kFold = RecordingInto(
      mod, InternedGenPrefix(),
      [this, mod](const Expr* e) { return EvalConstTypeRefCompare(e, mod); });
  type_ref_mod_ = mod;
  WalkItemExprsForTypeRefArg(item);
  FoldItemTypeRefCompares(item, kFold);
  ReportItemTypeParamErrors(*item, {mod->params, typedefs_, class_names_},
                            {typedefs_, unit_, class_names_}, diag_);
  if (ElaborateDeclItem(item, mod)) return;
  auto resolve = [&](DataType& dt, SourceLoc loc) {
    ResolveTypeRef(dt, loc, mod);
  };
  ResolveProceduralTypeRefs(
      item, ResolverAmongLocals(mod, resolve), arena_,
      [&](Stmt* s, std::span<const ProceduralLocal> locals) {
        InLocals(locals, [&] {
          CheckDynamicElementArgsOfStmt(s, mod);
          FoldTypeRefComparesOfStmt(s, kFold);
        });
      });
  auto elaborate_let = [&](ModuleItem* let) { ElaborateLetFormals(let, mod); };
  ForEachBlockLet(item->body, elaborate_let);
  for (const Stmt* s : item->func_body_stmts) ForEachBlockLet(s, elaborate_let);
  ElaborateBehavioralItem(item, mod);
}

void Elaborator::ElaborateModuleClassDecl(ModuleItem* item, RtlirModule* mod) {
  RecordClassDecl(item, mod, class_names_, parameterized_class_names_);
  typedefs_.erase(item->name);
  td_array_dims_.erase(item->name);
  if (item->class_decl == nullptr) return;
  module_classes_[item->class_decl->name] = item->class_decl;
  if (!gen_block_path_.empty()) {
    mod->gen_block_classes.push_back({item->class_decl, gen_block_path_});
  }
  RegisterClassTypedefKeys(item->class_decl, item->class_decl->name,
                           {unit_, typedefs_, td_array_dims_, arena_});
  RegisterModuleClassParams(item->class_decl, BuildParamScope(mod),
                            cu_param_scope_, arena_, diag_);
  ResolveClassMethodFormalTypes(item->class_decl, typedefs_, arena_);
  auto resolve = [&](DataType& dt, SourceLoc loc) {
    ResolveTypeRef(dt, loc, mod);
  };
  const TypeRefCompareFolder kFold = RecordingInto(
      mod, {},
      [this, mod](const Expr* e) { return EvalConstTypeRefCompare(e, mod); });
  ResolveClassTypeRefs(*item->class_decl, ResolverAmongLocals(mod, resolve),
                       unit_, arena_,
                       [&](Stmt* s, std::span<const ProceduralLocal> locals) {
                         InLocals(locals, [&] {
                           CheckDynamicElementArgsOfStmt(s, mod);
                           FoldTypeRefComparesOfStmt(s, kFold);
                         });
                       });
  auto elaborate_let = [&](ModuleItem* let) { ElaborateLetFormals(let, mod); };
  ForEachClassBodyItem(item->class_decl, [&](const ModuleItem* method) {
    for (const Stmt* s : method->func_body_stmts)
      ForEachBlockLet(s, elaborate_let);
  });
}

bool Elaborator::ElaborateDeclItem(ModuleItem* item, RtlirModule* mod) {
  auto make_implicit_net = [&](std::string_view n, SourceLoc l) {
    MaybeCreateImplicitNet(n, l, mod);
  };
  switch (item->kind) {
    case ModuleItemKind::kNetDecl:
      ElaborateNetDecl(item, mod);
      return true;
    case ModuleItemKind::kVarDecl:
      ElaborateVarDecl(item, mod);
      return true;
    case ModuleItemKind::kContAssign:
      ElaborateContAssign(item, mod);
      return true;
    case ModuleItemKind::kModuleInst:
      ElaborateModuleInst(item, mod);
      return true;
    case ModuleItemKind::kParamDecl:
      ElaborateParamDecl(item, mod);
      return true;
    case ModuleItemKind::kTypedef:
      ElaborateTypedef(item, mod);
      return true;
    case ModuleItemKind::kNettypeDecl:
      ElaborateNettypeDecl(item, mod);
      return true;
    case ModuleItemKind::kGateInst:
      CheckGateInstNameDiagnostics(item, diag_);
      DeclareInModuleNameSpace(item->gate_inst_name, item->loc);
      CreateImplicitNetsForTerminals(item->gate_terminals, item->loc,
                                     make_implicit_net);
      CheckPrimitiveTerminals(item, mod);
      ValidateBidirectionalSwitchConnections(item, mod, diag_,
                                             nettype_canonical_);
      ElaborateGateInst(item, mod, arena_, BuildParamScope(mod));
      RecordGateOutputDrivers(item);
      ResolveInterconnectPrimitiveTerminals(item->gate_terminals, mod);
      return true;
    case ModuleItemKind::kUdpInst:
      DeclareInModuleNameSpace(item->gate_inst_name, item->loc);
      CreateImplicitNetsForTerminals(item->gate_terminals, item->loc,
                                     make_implicit_net);
      CheckPrimitiveTerminals(item, mod);
      ElaborateUdpInst(item, mod);
      ResolveInterconnectPrimitiveTerminals(item->gate_terminals, mod);
      return true;
    case ModuleItemKind::kSpecparam:
      specparam_names_.insert(item->name);
      const_names_.insert(item->name);
      ElaborateSpecparam(item, mod);
      return true;
    case ModuleItemKind::kAlias: {
      CreateImplicitNetsForTerminals(item->alias_nets, item->loc,
                                     make_implicit_net);
      ValidateAlias(item, mod);
      RtlirAlias alias;
      alias.nets = item->alias_nets;
      mod->aliases.push_back(alias);
      return true;
    }
    case ModuleItemKind::kImportDecl:
      ApplyBodyImport(item->import_item);
      RecordImportDecl(item, mod);
      return true;
    case ModuleItemKind::kClassDecl:
      ElaborateModuleClassDecl(item, mod);
      return true;
    default:
      return false;
  }
}

void Elaborator::AddInferenceCallees(const Stmt* body) {
  const CompilationUnit& unit = *unit_;
  const std::function<const ModuleDecl*(std::string_view)> kFind =
      [this](std::string_view name) -> const ModuleDecl* {
    return FindModuleInScope(name);
  };
  AddScopedCallFunctions(body, {module_decl_path_, unit, kFind}, arena_,
                         inference_funcs_);
}

void Elaborator::AddProcedure(ModuleItem* item, RtlirModule* mod,
                              RtlirProcessKind kind) {
  ElaborateProceduralConcurrentAssertions(item, mod, property_registry_, arena_,
                                          diag_);
  ReportUnclockedLetSampledValues(item, mod, diag_);
  std::vector<ProceduralCheckerSite> sites;
  for (CheckerInstantiationInProcedure& site :
       CheckerInstantiationsIn(item->body, diag_)) {
    ModuleItem* inst = site.stmt->decl_item;
    ModuleDecl* child = FindModuleInScope(inst->inst_module);
    if (child == nullptr) child = PackageCheckerNamedBy(inst, mod, unit_);
    if (!AdmitProceduralCheckerInstance(inst, child, mod, diag_)) continue;
    const std::unordered_set<std::string_view> kAutomatics =
        CollectItemAutomaticVarNames(item);
    if (child != nullptr) {
      ValidateProceduralCheckerActuals(inst, child, kAutomatics, diag_);
    }
    ElaborateModuleInst(inst, mod);
    mod->children.back().is_procedural = true;
    mod->children.back().procedure_locals = std::move(site.locals);
    mod->children.back().procedure_automatics.assign(kAutomatics.begin(),
                                                     kAutomatics.end());
    FillInferredCheckerDefaults(mod->children.back(),
                                InferredInProcedure(item, mod), arena_);
    sites.push_back({site.stmt, ScopedName(inst->inst_name)});
  }
  bool infers = kind != RtlirProcessKind::kInitial;
  if (infers) AddInferenceCallees(item->body);
  const std::unordered_set<std::string> kTasks =
      kind == RtlirProcessKind::kAlways ? ReachableTaskNames()
                                        : std::unordered_set<std::string>{};
  const ProcessBuildEnv kEnv{arena_,
                             diag_,
                             infers ? &inference_funcs_ : nullptr,
                             infers ? &const_names_ : nullptr,
                             module_global_clocking_event_,
                             &kTasks};
  AddProcess(kind, item, mod, kEnv, BuildParamScope(mod));
  mod->processes.back().checker_instances = std::move(sites);
}

bool Elaborator::ElaborateBehavioralItem(ModuleItem* item, RtlirModule* mod) {
  const ProcessBuildEnv kNoInferenceEnv{
      .arena = arena_,
      .diag = diag_,
      .global_clocking_event = module_global_clocking_event_};
  switch (item->kind) {
    case ModuleItemKind::kInitialBlock:
      AddProcedure(item, mod, RtlirProcessKind::kInitial);
      return true;
    case ModuleItemKind::kFinalBlock:
      AddProcess(RtlirProcessKind::kFinal, item, mod, kNoInferenceEnv,
                 BuildParamScope(mod));
      return true;
    case ModuleItemKind::kAlwaysBlock:
    case ModuleItemKind::kAlwaysCombBlock:
    case ModuleItemKind::kAlwaysFFBlock:
    case ModuleItemKind::kAlwaysLatchBlock:
      AddProcedure(item, mod, MapAlwaysKind(item->always_kind));
      return true;
    case ModuleItemKind::kGenerateIf:
    case ModuleItemKind::kGenerateCase:
    case ModuleItemKind::kGenerateFor:
      pending_generates_.push_back(
          {item, mod, typedefs_, cu_param_scope_, func_decls_,
           property_registry_, config_inst_path_, current_library_,
           interface_inst_types_, module_decl_path_, td_array_dims_});
      return true;
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kTaskDecl:
      DeclareInModuleNameSpace(item->name, item->loc);
      ReportMisplacedOverrideSpecifiers(*item, diag_);
      ValidateFunctionBody(item);
      ValidateFunctionArgDefaultsScope(item);
      ResolveFormalAggregateTypes(item, typedefs_, arena_);
      ElaborateSubroutineConcurrentAssertions(item, mod, property_registry_,
                                              arena_, diag_);
      mod->function_decls.push_back(WithGlobalClockSubstituted(
          item, module_global_clocking_event_, arena_));
      return true;
    case ModuleItemKind::kElabSystemTask:
      ValidateElabSystemTask(item, mod);
      return true;
    case ModuleItemKind::kDpiImport:
      if (dpi_import_names_.insert(ScopedName(item->name)).second) {
        DeclareInModuleNameSpace(item->name, item->loc);
      }
      ValidateDpiImport(item);
      mod->dpi_import_decls.push_back(item);
      return true;
    case ModuleItemKind::kLetDecl:
      ElaborateLetFormals(item, mod);
      let_names_.insert(item->name);
      mod->let_decls.push_back(item);
      if (!gen_block_path_.empty()) {
        mod->gen_block_lets.push_back(
            {item, gen_block_path_, gen_prefix_scopes_});
      }
      return true;
    case ModuleItemKind::kSpecifyBlock:
      RegisterSpecifyBlockSpecparams(item, mod, typedefs_,
                                     {specparam_names_, const_names_}, diag_);
      mod->specify_blocks.push_back(item);
      return true;
    case ModuleItemKind::kCovergroupDecl:
      if (!item->covergroup_extends_base.empty()) {
        diag_.Error(item->loc,
                    "a covergroup may only use 'extends' inside a class",
                    Subclause("19.3"));
      }
      mod->let_decls.push_back(item);
      return true;
    case ModuleItemKind::kDpiExport:
      mod->dpi_export_decls.push_back(item);
      return true;
    default:
      return ElaborateAssertionItem(item, mod);
  }
}

}  // namespace delta
