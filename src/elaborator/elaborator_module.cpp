#include <algorithm>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/checker_instance_binding.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/global_clock_assertion_event.h"
#include "elaborator/global_clocking_declaration.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/sensitivity.h"
#include "elaborator/time_literal_scale.h"
#include "elaborator/unit_scope_switch.h"
#include "elaborator/uwire_drivers.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

static uint32_t NamedSignalWidth(std::string_view name,
                                 const RtlirModule* mod) {
  for (const auto& v : mod->variables)
    if (v.name == name) return v.width;
  for (const auto& n : mod->nets)
    if (n.name == name) return n.width;
  return 0;
}

static uint32_t ExplicitPortSelectWidth(const Expr* expr,
                                        const ScopeMap& scope) {
  if (expr->index_end == nullptr) return 1;
  if (expr->is_part_select_plus || expr->is_part_select_minus) {
    auto w = ConstEvalInt(expr->index_end, scope);
    return (w && *w > 0) ? static_cast<uint32_t>(*w) : 0;
  }
  auto hi = ConstEvalInt(expr->index, scope);
  auto lo = ConstEvalInt(expr->index_end, scope);
  if (!hi || !lo) return 0;
  int64_t span = (*hi >= *lo) ? (*hi - *lo + 1) : (*lo - *hi + 1);
  return static_cast<uint32_t>(span);
}

static uint32_t ExplicitPortExprWidth(const Expr* expr, const RtlirModule* mod,
                                      const ScopeMap& scope) {
  if (!expr) return 0;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      return NamedSignalWidth(expr->text, mod);
    case ExprKind::kConcatenation: {
      uint32_t total = 0;
      for (const auto* el : expr->elements)
        total += ExplicitPortExprWidth(el, mod, scope);
      return total;
    }
    case ExprKind::kSelect:
      return ExplicitPortSelectWidth(expr, scope);
    default:
      return 0;
  }
}

static bool ExplicitPortExprSigned(const Expr* expr, const RtlirModule* mod) {
  if (!expr || expr->kind != ExprKind::kIdentifier) return false;
  for (const auto& v : mod->variables)
    if (v.name == expr->text) return v.is_signed;
  for (const auto& n : mod->nets)
    if (n.name == expr->text) return n.is_signed;
  return false;
}

static bool ExplicitPortExprIs4state(const Expr* expr, const RtlirModule* mod) {
  while (expr->kind == ExprKind::kSelect) expr = expr->base;
  if (expr->kind == ExprKind::kConcatenation) {
    return std::ranges::any_of(expr->elements, [&](const Expr* el) {
      return ExplicitPortExprIs4state(el, mod);
    });
  }
  for (const auto& v : mod->variables) {
    if (v.name == expr->text) return v.is_4state;
  }
  return true;
}

static void ResolveExplicitPortTypes(const ModuleDecl* decl, RtlirModule* mod,
                                     const ScopeMap& scope) {
  for (const auto& src : decl->ports) {
    if (!src.is_explicit_named || !src.port_expr || src.name.empty()) continue;
    uint32_t w = ExplicitPortExprWidth(src.port_expr, mod, scope);
    for (auto& rp : mod->ports) {
      if (rp.name != src.name) continue;
      rp.port_expr = src.port_expr;
      if (w == 0) break;
      rp.type_kind = ExplicitPortExprIs4state(src.port_expr, mod)
                         ? DataTypeKind::kLogic
                         : DataTypeKind::kBit;
      rp.width = w;
      rp.is_signed = ExplicitPortExprSigned(src.port_expr, mod);
      break;
    }
  }
}

static void ReportParamsMissingValue(const ModuleDecl* decl,
                                     const RtlirModule* mod, DiagEngine& diag) {
  for (const auto& pd : mod->params) {
    if (pd.is_localparam || pd.is_type_param) continue;
    if (pd.default_value != nullptr) continue;
    if (pd.from_override) continue;
    diag.Error(decl->range.start,
               std::format("parameter '{}' of '{}' has no default value and "
                           "no override at instantiation",
                           pd.name, decl->name),
               Subclause("6.20.1"));
  }
}

static void InitInterfaceHeader(RtlirModule* mod, const ModuleDecl* decl) {
  mod->is_interface = (decl->decl_kind == ModuleDeclKind::kInterface);
  if (mod->is_interface) {
    mod->modports.assign(decl->modports.begin(), decl->modports.end());
  }
}

static void InitRtlirModuleHeader(RtlirModule* mod, const ModuleDecl* decl,
                                  const CompilationUnit* unit,
                                  const ScopeMap& unit_params,
                                  DiagEngine& diag) {
  mod->name = decl->name;
  mod->loc = decl->range.start;
  mod->library = decl->library;
  mod->fsms = decl->fsms;
  mod->has_param_port_list = decl->has_param_port_list;
  mod->is_program = (decl->decl_kind == ModuleDeclKind::kProgram);
  InitInterfaceHeader(mod, decl);
  mod->is_checker = (decl->decl_kind == ModuleDeclKind::kChecker);
  mod->is_automatic = decl->is_automatic;
  mod->decl = decl;
  if (decl->has_module_directives) {
    mod->default_decay_time = decl->default_decay_time;
    mod->default_decay_time_infinite = decl->default_decay_time_infinite;
    mod->default_decay_time_is_real = decl->default_decay_time_is_real;
    mod->default_decay_time_real = decl->default_decay_time_real;
    mod->default_trireg_strength = decl->default_trireg_strength;
    mod->has_default_trireg_strength = decl->has_default_trireg_strength;
    mod->delay_mode = decl->delay_mode;
  } else {
    mod->default_decay_time = unit->default_decay_time;
    mod->default_decay_time_infinite = unit->default_decay_time_infinite;
    mod->default_decay_time_is_real = unit->default_decay_time_is_real;
    mod->default_decay_time_real = unit->default_decay_time_real;
    mod->default_trireg_strength = unit->default_trireg_strength;
    mod->has_default_trireg_strength = unit->has_default_trireg_strength;
    mod->delay_mode = unit->delay_mode_directive;
  }
  mod->default_nettype =
      decl->has_net_directives ? decl->default_nettype : unit->default_nettype;
  mod->unconnected_drive = decl->has_net_directives ? decl->unconnected_drive
                                                    : unit->unconnected_drive;
  mod->attrs = ResolveAttributes(decl->attrs, diag, unit_params);
  mod->timescale = ModuleTimescale(decl, *unit);

  RtlirImport std_import;
  std_import.package_name = "std";
  std_import.is_wildcard = true;
  mod->imports.push_back(std_import);
}

void Elaborator::ResetItemElaborationState() {
  forward_typedef_kinds_.clear();
  declared_names_.clear();
  dpi_import_names_.clear();
  net_names_.clear();
  cont_assign_targets_.clear();
  uwire_drivers_.Clear();
  proc_assign_targets_.clear();
  var_types_.clear();
  var_array_info_.clear();
  net_array_info_.clear();
  specparam_names_.clear();
  enum_var_names_.clear();
  enum_member_names_.clear();
  const_names_.clear();
  const_var_names_.clear();
  class_var_names_.clear();
  class_var_types_.clear();
  var_init_names_.clear();
  output_port_targets_.clear();
  force_release_targets_.clear();
  nettype_net_names_.clear();
  interconnect_names_.clear();
  scalar_var_names_.clear();
  real_var_names_.clear();
  real_param_names_.clear();
  var_select_shapes_.clear();
  var_named_types_.clear();
  alias_bit_pairs_.clear();
  non_ansi_complete_ports_.clear();
  non_ansi_partial_ports_.clear();
  non_ansi_signed_ports_.clear();
  ansi_port_names_.clear();
  clocking_signals_.clear();
  interface_inst_types_.clear();
  vi_var_interface_types_.clear();
  vi_var_modports_.clear();
  vi_var_param_values_.clear();
  interface_inst_param_values_.clear();
  checker_inst_names_.clear();
  program_inst_names_.clear();
  auto_task_func_names_.clear();
  nested_module_decls_.clear();
  enclosing_nested_decls_.clear();
  task_names_.clear();
  let_names_.clear();
  sequence_names_.clear();
  func_decls_.clear();
  inference_funcs_ = InferenceFuncs{};
}

struct ItemElaborationStateSaver {
  decltype(Elaborator::forward_typedef_kinds_) forward_typedef_kinds;
  decltype(Elaborator::declared_names_) declared_names;
  decltype(Elaborator::dpi_import_names_) dpi_import_names;
  decltype(Elaborator::net_names_) net_names;
  decltype(Elaborator::cont_assign_targets_) cont_assign_targets;
  decltype(Elaborator::uwire_drivers_) uwire_drivers;
  decltype(Elaborator::proc_assign_targets_) proc_assign_targets;
  decltype(Elaborator::var_types_) var_types;
  decltype(Elaborator::var_array_info_) var_array_info;
  decltype(Elaborator::net_array_info_) net_array_info;
  decltype(Elaborator::specparam_names_) specparam_names;
  decltype(Elaborator::enum_var_names_) enum_var_names;
  decltype(Elaborator::enum_member_names_) enum_member_names;
  decltype(Elaborator::const_names_) const_names;
  decltype(Elaborator::const_var_names_) const_var_names;
  decltype(Elaborator::class_var_names_) class_var_names;
  decltype(Elaborator::class_var_types_) class_var_types;
  decltype(Elaborator::var_init_names_) var_init_names;
  decltype(Elaborator::output_port_targets_) output_port_targets;
  decltype(Elaborator::force_release_targets_) force_release_targets;
  decltype(Elaborator::nettype_net_names_) nettype_net_names;
  decltype(Elaborator::interconnect_names_) interconnect_names;
  decltype(Elaborator::scalar_var_names_) scalar_var_names;
  decltype(Elaborator::real_var_names_) real_var_names;
  decltype(Elaborator::real_param_names_) real_param_names;
  decltype(Elaborator::var_select_shapes_) var_select_shapes;
  decltype(Elaborator::var_named_types_) var_named_types;
  decltype(Elaborator::alias_bit_pairs_) alias_bit_pairs;
  decltype(Elaborator::non_ansi_complete_ports_) non_ansi_complete_ports;
  decltype(Elaborator::non_ansi_partial_ports_) non_ansi_partial_ports;
  decltype(Elaborator::non_ansi_signed_ports_) non_ansi_signed_ports;
  decltype(Elaborator::ansi_port_names_) ansi_port_names;
  decltype(Elaborator::clocking_signals_) clocking_signals;
  decltype(Elaborator::interface_inst_types_) interface_inst_types;
  decltype(Elaborator::vi_var_interface_types_) vi_var_interface_types;
  decltype(Elaborator::vi_var_modports_) vi_var_modports;
  decltype(Elaborator::vi_var_param_values_) vi_var_param_values;
  decltype(Elaborator::interface_inst_param_values_) interface_inst_param_vals;
  decltype(Elaborator::checker_inst_names_) checker_inst_names;
  decltype(Elaborator::program_inst_names_) program_inst_names;
  decltype(Elaborator::auto_task_func_names_) auto_task_func_names;
  decltype(Elaborator::nested_module_decls_) nested_module_decls;
  decltype(Elaborator::enclosing_nested_decls_) enclosing_nested_decls;
  decltype(Elaborator::task_names_) task_names;
  decltype(Elaborator::let_names_) let_names;
  decltype(Elaborator::sequence_names_) sequence_names;
  decltype(Elaborator::property_registry_) property_registry;
  decltype(Elaborator::func_decls_) func_decls;
  decltype(Elaborator::inference_funcs_) inference_funcs;

  struct ScopeMaps {
    decltype(Elaborator::typedefs_) typedefs;
    decltype(Elaborator::cu_param_scope_) cu_param_scope;
    decltype(Elaborator::td_array_dims_) td_array_dims;
  } scope_maps;

  explicit ItemElaborationStateSaver(Elaborator& e)
      : scope_maps{e.typedefs_, e.cu_param_scope_, e.td_array_dims_} {
    TakeObjectState(e);
    TakePortAndDeclarationState(e);
    e.ResetItemElaborationState();
  }

  void TakeObjectState(Elaborator& e) {
    forward_typedef_kinds = std::move(e.forward_typedef_kinds_);
    declared_names = std::move(e.declared_names_);
    dpi_import_names = std::move(e.dpi_import_names_);
    net_names = std::move(e.net_names_);
    cont_assign_targets = std::move(e.cont_assign_targets_);
    uwire_drivers = std::move(e.uwire_drivers_);
    proc_assign_targets = std::move(e.proc_assign_targets_);
    var_types = std::move(e.var_types_);
    var_array_info = std::move(e.var_array_info_);
    net_array_info = std::move(e.net_array_info_);
    specparam_names = std::move(e.specparam_names_);
    enum_var_names = std::move(e.enum_var_names_);
    enum_member_names = std::move(e.enum_member_names_);
    const_names = std::move(e.const_names_);
    const_var_names = std::move(e.const_var_names_);
    class_var_names = std::move(e.class_var_names_);
    class_var_types = std::move(e.class_var_types_);
    var_init_names = std::move(e.var_init_names_);
    output_port_targets = std::move(e.output_port_targets_);
    force_release_targets = std::move(e.force_release_targets_);
    nettype_net_names = std::move(e.nettype_net_names_);
    interconnect_names = std::move(e.interconnect_names_);
    scalar_var_names = std::move(e.scalar_var_names_);
    real_var_names = std::move(e.real_var_names_);
    real_param_names = std::move(e.real_param_names_);
    var_select_shapes = std::move(e.var_select_shapes_);
    var_named_types = std::move(e.var_named_types_);
    alias_bit_pairs = std::move(e.alias_bit_pairs_);
  }

  void TakePortAndDeclarationState(Elaborator& e) {
    non_ansi_complete_ports = std::move(e.non_ansi_complete_ports_);
    non_ansi_partial_ports = std::move(e.non_ansi_partial_ports_);
    non_ansi_signed_ports = std::move(e.non_ansi_signed_ports_);
    ansi_port_names = std::move(e.ansi_port_names_);
    clocking_signals = std::move(e.clocking_signals_);
    interface_inst_types = std::move(e.interface_inst_types_);
    vi_var_interface_types = std::move(e.vi_var_interface_types_);
    vi_var_modports = std::move(e.vi_var_modports_);
    vi_var_param_values = std::move(e.vi_var_param_values_);
    interface_inst_param_vals = std::move(e.interface_inst_param_values_);
    checker_inst_names = std::move(e.checker_inst_names_);
    program_inst_names = std::move(e.program_inst_names_);
    auto_task_func_names = std::move(e.auto_task_func_names_);
    nested_module_decls = std::move(e.nested_module_decls_);
    enclosing_nested_decls = std::move(e.enclosing_nested_decls_);
    task_names = std::move(e.task_names_);
    let_names = std::move(e.let_names_);
    sequence_names = std::move(e.sequence_names_);
    property_registry = std::move(e.property_registry_);
    func_decls = std::move(e.func_decls_);
    inference_funcs = std::move(e.inference_funcs_);
  }

  void RestoreScopeMaps(Elaborator& e) {
    for (const auto& [name, dtype] : e.typedefs_)
      e.all_typedefs_.insert_or_assign(name, dtype);
    for (const auto& [name, val] : e.cu_param_scope_)
      e.all_cu_param_scope_.insert_or_assign(name, val);
    for (const auto& [name, dims] : e.td_array_dims_)
      e.all_td_array_dims_.insert_or_assign(name, dims);
    e.typedefs_ = std::move(scope_maps.typedefs);
    e.cu_param_scope_ = std::move(scope_maps.cu_param_scope);
    e.td_array_dims_ = std::move(scope_maps.td_array_dims);
  }

  void Restore(Elaborator& e) {
    PutBackObjectState(e);
    PutBackPortAndDeclarationState(e);
    RestoreScopeMaps(e);
  }

  void PutBackObjectState(Elaborator& e) {
    e.forward_typedef_kinds_ = std::move(forward_typedef_kinds);
    e.declared_names_ = std::move(declared_names);
    e.dpi_import_names_ = std::move(dpi_import_names);
    e.net_names_ = std::move(net_names);
    e.cont_assign_targets_ = std::move(cont_assign_targets);
    e.uwire_drivers_ = std::move(uwire_drivers);
    e.proc_assign_targets_ = std::move(proc_assign_targets);
    e.var_types_ = std::move(var_types);
    e.var_array_info_ = std::move(var_array_info);
    e.net_array_info_ = std::move(net_array_info);
    e.specparam_names_ = std::move(specparam_names);
    e.enum_var_names_ = std::move(enum_var_names);
    e.enum_member_names_ = std::move(enum_member_names);
    e.const_names_ = std::move(const_names);
    e.const_var_names_ = std::move(const_var_names);
    e.class_var_names_ = std::move(class_var_names);
    e.class_var_types_ = std::move(class_var_types);
    e.var_init_names_ = std::move(var_init_names);
    e.output_port_targets_ = std::move(output_port_targets);
    e.force_release_targets_ = std::move(force_release_targets);
    e.nettype_net_names_ = std::move(nettype_net_names);
    e.interconnect_names_ = std::move(interconnect_names);
    e.scalar_var_names_ = std::move(scalar_var_names);
    e.real_var_names_ = std::move(real_var_names);
    e.real_param_names_ = std::move(real_param_names);
    e.var_select_shapes_ = std::move(var_select_shapes);
    e.var_named_types_ = std::move(var_named_types);
    e.alias_bit_pairs_ = std::move(alias_bit_pairs);
  }

  void PutBackPortAndDeclarationState(Elaborator& e) {
    e.non_ansi_complete_ports_ = std::move(non_ansi_complete_ports);
    e.non_ansi_partial_ports_ = std::move(non_ansi_partial_ports);
    e.non_ansi_signed_ports_ = std::move(non_ansi_signed_ports);
    e.ansi_port_names_ = std::move(ansi_port_names);
    e.clocking_signals_ = std::move(clocking_signals);
    e.interface_inst_types_ = std::move(interface_inst_types);
    e.vi_var_interface_types_ = std::move(vi_var_interface_types);
    e.vi_var_modports_ = std::move(vi_var_modports);
    e.vi_var_param_values_ = std::move(vi_var_param_values);
    e.interface_inst_param_values_ = std::move(interface_inst_param_vals);
    e.checker_inst_names_ = std::move(checker_inst_names);
    e.program_inst_names_ = std::move(program_inst_names);
    e.auto_task_func_names_ = std::move(auto_task_func_names);
    e.nested_module_decls_ = std::move(nested_module_decls);
    e.enclosing_nested_decls_ = std::move(enclosing_nested_decls);
    e.task_names_ = std::move(task_names);
    e.let_names_ = std::move(let_names);
    e.sequence_names_ = std::move(sequence_names);
    e.property_registry_ = std::move(property_registry);
    e.func_decls_ = std::move(func_decls);
    e.inference_funcs_ = std::move(inference_funcs);
  }
};

static std::vector<std::unordered_set<std::string_view>>
EnterEnclosingScopeChain(
    std::vector<std::unordered_set<std::string_view>>& chain,
    std::unordered_set<std::string_view>& pending, bool& has_pending) {
  std::vector<std::unordered_set<std::string_view>> saved = std::move(chain);
  chain.clear();
  if (has_pending) {
    chain = saved;
    chain.push_back(std::move(pending));
    pending.clear();
    has_pending = false;
  }
  return saved;
}

template <class Scopes>
static const std::vector<EventExpr>* EnterGlobalClockingChain(
    Scopes& scopes, const std::vector<EventExpr>* own_gclk,
    const std::string& inst_path, Arena& arena) {
  if (own_gclk != nullptr) scopes.push_back({own_gclk, inst_path});
  if (scopes.empty()) return nullptr;
  const auto& nearest = scopes.back();
  return EffectiveGlobalClockingEvent(nearest.events, nearest.inst_path,
                                      inst_path, arena);
}

RtlirModule* Elaborator::ElaborateModule(const ModuleDecl* decl,
                                         const ParamList& params) {
  UnitScopeTables::Switch unit_scope(*this, decl);
  auto* mod = arena_.Create<RtlirModule>();
  if (!units_.views.empty()) mod->unit_index = static_cast<int>(units_.current);
  InitRtlirModuleHeader(mod, decl, unit_, cu_param_scope_, diag_);
  mod->config = active_config_;

  ItemElaborationStateSaver saved_item_state(*this);
  GenerateScopeSaver saved_generate_scope(*this);

  std::vector<std::unordered_set<std::string_view>> saved_enclosing =
      EnterEnclosingScopeChain(enclosing_scope_names_, pending_enclosing_scope_,
                               has_pending_enclosing_scope_);
  TakeNestedDeclInheritance();

  std::string saved_library =
      std::exchange(current_library_, std::string(decl->library));

  ApplyCompilationUnitImports(decl, mod);
  ApplyHeaderImports(decl);
  ImportedEnumCtx enum_ctx{unit_, arena_, typedefs_, enum_member_names_};
  RegisterImportedEnumLiterals(decl, mod, enum_ctx);
  RegisterCuEnumLiterals(decl, mod, enum_ctx);

  module_decl_path_.push_back(decl);
  ElaborateParamPortList(decl, params, mod);
  if (decl->decl_kind == ModuleDeclKind::kChecker) {
    mod->constant_formals = CheckerConstantFormals(
        decl, std::exchange(pending_checker_actuals_, {}),
        BuildParamScope(mod));
    SetCheckerFreeVariables(decl, mod);
    checker_tree_actuals_[mod] =
        std::exchange(pending_checker_tree_actuals_, {});
  }

  const InstanceParamAssignments kBodyAssignments{
      params, RegisteredModuleScope(), RegisteredModule(),
      InnermostScope(RegisteredGenPrefixes())};
  BodyParamAssignmentsGuard body_assignments_guard(
      decl->has_param_port_list ? nullptr : &kBodyAssignments);

  ReportParamsMissingValue(decl, mod, diag_);

  ElaboratePorts(decl, mod);

  CheckGenerateConstructs(decl);
  AssignGenerateBlockNames(decl);

  bool saved_global_clocking_in_scope = std::exchange(
      global_clocking_in_scope_,
      global_clocking_in_scope_ || ModuleDeclaresGlobalClocking(decl));

  const std::vector<EventExpr>* own_gclk = ModuleGlobalClockingEvent(decl);
  const std::vector<EventExpr>* saved_global_clocking_event =
      std::exchange(module_global_clocking_event_,
                    EnterGlobalClockingChain(global_clocking_scopes_, own_gclk,
                                             current_inst_path_, arena_));
  if (decl->decl_kind == ModuleDeclKind::kChecker) {
    ResolveGlobalClockInCheckerActuals(checker_tree_actuals_[mod],
                                       global_clocking_scopes_,
                                       current_inst_path_, arena_);
  }

  ElaborateItems(decl, mod);
  module_decl_path_.pop_back();
  ResolveExplicitPortTypes(decl, mod, BuildParamScope(mod));
  module_global_clocking_event_ = saved_global_clocking_event;
  if (own_gclk != nullptr) global_clocking_scopes_.pop_back();
  global_clocking_in_scope_ = saved_global_clocking_in_scope;
  current_library_ = std::move(saved_library);
  enclosing_scope_names_ = std::move(saved_enclosing);
  module_scope_names_[mod] = {declared_names_,
                              net_names_,
                              cont_assign_targets_,
                              proc_assign_targets_,
                              var_init_names_,
                              uwire_drivers_,
                              interconnect_names_,
                              force_release_targets_,
                              std::move(var_types_),
                              std::move(class_var_types_),
                              std::move(scalar_var_names_),
                              std::move(real_var_names_),
                              std::move(real_param_names_),
                              std::move(var_select_shapes_),
                              std::move(class_var_names_)};
  saved_item_state.Restore(*this);
  return mod;
}

}  // namespace delta
