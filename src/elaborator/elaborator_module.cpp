#include <cstdint>
#include <cstdlib>
#include <format>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/global_clock_assertion_event.h"
#include "elaborator/rtlir.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

// §23.2.2.3: an explicitly named port (.name(expr)) takes the self-determined
// data type of its connection expression. Resolve the expression's width
// against the module's already-elaborated variables and nets. Returns 0 when
// the width cannot be determined here, leaving the port's default untouched.
// The declared width of the variable or net named `name` in `mod`, or 0 when
// the module declares no such signal.
static uint32_t NamedSignalWidth(std::string_view name,
                                 const RtlirModule* mod) {
  for (const auto& v : mod->variables)
    if (v.name == name) return v.width;
  for (const auto& n : mod->nets)
    if (n.name == name) return n.width;
  return 0;
}

// A bit-select of a vector yields a single bit. A part-select's width is
// self-determined from the select bounds alone: an indexed part-select (+:/-:)
// is as wide as its constant width operand, and a ranged select spans the
// inclusive distance between its two constant bounds. The LRM example
// `.P1(r[3:0])` connects to a 4-bit slice regardless of r's width.
static uint32_t ExplicitPortSelectWidth(const Expr* expr) {
  if (expr->index_end == nullptr) return 1;
  if (expr->is_part_select_plus || expr->is_part_select_minus) {
    auto w = ConstEvalInt(expr->index_end);
    return (w && *w > 0) ? static_cast<uint32_t>(*w) : 0;
  }
  auto hi = ConstEvalInt(expr->index);
  auto lo = ConstEvalInt(expr->index_end);
  if (!hi || !lo) return 0;
  int64_t span = (*hi >= *lo) ? (*hi - *lo + 1) : (*lo - *hi + 1);
  return static_cast<uint32_t>(span);
}

static uint32_t ExplicitPortExprWidth(const Expr* expr,
                                      const RtlirModule* mod) {
  if (!expr) return 0;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      return NamedSignalWidth(expr->text, mod);
    case ExprKind::kConcatenation: {
      uint32_t total = 0;
      for (const auto* el : expr->elements)
        total += ExplicitPortExprWidth(el, mod);
      return total;
    }
    case ExprKind::kSelect:
      return ExplicitPortSelectWidth(expr);
    default:
      return 0;
  }
}

// The self-determined signedness of an explicit port expression: a simple
// reference adopts the referenced object's signedness; composite expressions
// such as concatenations are unsigned.
static bool ExplicitPortExprSigned(const Expr* expr, const RtlirModule* mod) {
  if (!expr || expr->kind != ExprKind::kIdentifier) return false;
  for (const auto& v : mod->variables)
    if (v.name == expr->text) return v.is_signed;
  for (const auto& n : mod->nets)
    if (n.name == expr->text) return n.is_signed;
  return false;
}

// §23.2.2.3: apply the self-determined type of each explicitly named port's
// connection expression to the resolved port. The referenced declarations live
// in the module body, so this runs after the items have been elaborated.
static void ResolveExplicitPortTypes(const ModuleDecl* decl, RtlirModule* mod) {
  for (const auto& src : decl->ports) {
    if (!src.is_explicit_named || !src.port_expr || src.name.empty()) continue;
    uint32_t w = ExplicitPortExprWidth(src.port_expr, mod);
    if (w == 0) continue;
    for (auto& rp : mod->ports) {
      if (rp.name != src.name) continue;
      rp.type_kind = DataTypeKind::kLogic;
      rp.width = w;
      rp.is_signed = ExplicitPortExprSigned(src.port_expr, mod);
      break;
    }
  }
}

// §6.20: report every value parameter that ends up with neither a default
// expression nor an instantiation override.
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

// Initialize the standalone (non-port, non-item) header fields of a freshly
// created RtlirModule from its declaration.
static void InitRtlirModuleHeader(RtlirModule* mod, const ModuleDecl* decl,
                                  const CompilationUnit* unit,
                                  DiagEngine& diag) {
  mod->name = decl->name;
  mod->library = decl->library;
  mod->has_param_port_list = decl->has_param_port_list;
  mod->is_program = (decl->decl_kind == ModuleDeclKind::kProgram);
  mod->is_interface = (decl->decl_kind == ModuleDeclKind::kInterface);
  // Annex E: each of its directives applies to the modules that follow it,
  // so the values recorded at this module's header stand ahead of the unit's
  // last.
  if (decl->has_module_directives) {
    mod->default_decay_time = decl->default_decay_time;
    mod->default_decay_time_infinite = decl->default_decay_time_infinite;
    mod->default_trireg_strength = decl->default_trireg_strength;
    mod->has_default_trireg_strength = decl->has_default_trireg_strength;
    mod->delay_mode = decl->delay_mode;
  } else {
    mod->default_decay_time = unit->default_decay_time;
    mod->default_decay_time_infinite = unit->default_decay_time_infinite;
    mod->default_trireg_strength = unit->default_trireg_strength;
    mod->has_default_trireg_strength = unit->has_default_trireg_strength;
    mod->delay_mode = unit->delay_mode_directive;
  }
  mod->attrs = ResolveAttributes(decl->attrs, diag);

  // §20.4.1: capture the time unit/precision $timeunit/$timeprecision report
  // for this element. A local timeunit/timeprecision declaration wins;
  // otherwise the compilation unit's value applies, and absent both the 1 ns /
  // 1 ns default of the TimeScale struct stands in.
  if (decl->has_timeunit) {
    mod->timescale.unit = decl->time_unit;
    mod->timescale.magnitude = decl->time_unit_magnitude;
  } else if (unit->has_cu_timeunit) {
    mod->timescale.unit = unit->cu_time_unit;
    mod->timescale.magnitude = unit->cu_time_unit_magnitude;
  }
  if (decl->has_timeprecision) {
    mod->timescale.precision = decl->time_prec;
    mod->timescale.prec_magnitude = decl->time_prec_magnitude;
  } else if (unit->has_cu_timeprecision) {
    mod->timescale.precision = unit->cu_time_prec;
    mod->timescale.prec_magnitude = unit->cu_time_prec_magnitude;
  }

  RtlirImport std_import;
  std_import.package_name = "std";
  std_import.is_wildcard = true;
  mod->imports.push_back(std_import);
}

// Clears every per-module bookkeeping table before a module's items are
// elaborated. Lives beside ItemElaborationStateSaver (whose field set mirrors
// it exactly) so the two stay in sync.
void Elaborator::ResetItemElaborationState() {
  forward_typedef_kinds_.clear();
  declared_names_.clear();
  net_names_.clear();
  cont_assign_targets_.clear();
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
  alias_pairs_.clear();
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
  task_names_.clear();
  let_names_.clear();
  sequence_names_.clear();
  func_decls_.clear();
}

// Holds a snapshot of the per-module item-elaboration state. The constructor
// moves the state out of the elaborator (resetting it for the nested module
// about to be elaborated); Restore moves it back. The field set mirrors
// Elaborator::ResetItemElaborationState exactly, apart from the two named at
// the end of it; decltype is used so the field types track the members without
// naming the elaborator's private nested types.
struct ItemElaborationStateSaver {
  decltype(Elaborator::forward_typedef_kinds_) forward_typedef_kinds;
  decltype(Elaborator::declared_names_) declared_names;
  decltype(Elaborator::net_names_) net_names;
  decltype(Elaborator::cont_assign_targets_) cont_assign_targets;
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
  decltype(Elaborator::alias_pairs_) alias_pairs;
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
  decltype(Elaborator::task_names_) task_names;
  decltype(Elaborator::let_names_) let_names;
  decltype(Elaborator::sequence_names_) sequence_names;
  // §16.12: the registry of the module's own property and sequence
  // declarations, which an instance an item makes rebuilds for the module it
  // instantiates, so the items after the instance read their own module's
  // declarations only because it is put back.
  decltype(Elaborator::property_registry_) property_registry;
  decltype(Elaborator::func_decls_) func_decls;

  // §26.3 and §6.18: a name an import or a typedef declaration introduces
  // belongs to the scope it was written in, so what a module adds to typedefs_
  // and cu_param_scope_ is taken back out before the next module is elaborated.
  // Without this, `module a; import q::*; endmodule module b; word_t y;
  // endmodule` sizes b's y from a's import, and a typedef declared in a is
  // equally visible in b.
  //
  // These two are the exception to the field set above: they are copied and put
  // back rather than moved out and cleared, because they also hold the
  // compilation unit's own declarations. Elaborator::RegisterCuScopeItems fills
  // both with $unit's typedefs and parameters and with every package parameter
  // under its qualified key before any module is elaborated, and §3.12.1 makes
  // those visible to every design element in the unit. Clearing them would take
  // those away from the module about to be elaborated, so the copy keeps them
  // and drops only what that module added.
  // Elaborator::ResetItemElaborationState therefore does not name them.
  //
  // A module elaborated as a child instance still starts from its parent's
  // entry, which is what a lexically nested module (§23.4) requires and a
  // separately instantiated one does not; that is a different question from the
  // one settled here, which is what one module leaves behind for the next.
  decltype(Elaborator::typedefs_) typedefs;
  decltype(Elaborator::cu_param_scope_) cu_param_scope;

  explicit ItemElaborationStateSaver(Elaborator& e)
      : typedefs(e.typedefs_), cu_param_scope(e.cu_param_scope_) {
    forward_typedef_kinds = std::move(e.forward_typedef_kinds_);
    declared_names = std::move(e.declared_names_);
    net_names = std::move(e.net_names_);
    cont_assign_targets = std::move(e.cont_assign_targets_);
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
    alias_pairs = std::move(e.alias_pairs_);
    alias_bit_pairs = std::move(e.alias_bit_pairs_);
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
    task_names = std::move(e.task_names_);
    let_names = std::move(e.let_names_);
    sequence_names = std::move(e.sequence_names_);
    property_registry = std::move(e.property_registry_);
    func_decls = std::move(e.func_decls_);
    e.ResetItemElaborationState();
  }

  // Hands this module's typedefs and compilation-unit parameters back. What the
  // module added is kept in the design-wide unions, which a pass running after
  // every module reads, before the maps the next module reads are taken back to
  // what they were. insert_or_assign and not insert: two modules may declare
  // one name, and the design-wide tables named the last one before any of this
  // existed.
  void RestoreScopeMaps(Elaborator& e) {
    for (const auto& [name, dtype] : e.typedefs_)
      e.all_typedefs_.insert_or_assign(name, dtype);
    for (const auto& [name, val] : e.cu_param_scope_)
      e.all_cu_param_scope_.insert_or_assign(name, val);
    e.typedefs_ = std::move(typedefs);
    e.cu_param_scope_ = std::move(cu_param_scope);
  }

  void Restore(Elaborator& e) {
    e.forward_typedef_kinds_ = std::move(forward_typedef_kinds);
    e.declared_names_ = std::move(declared_names);
    e.net_names_ = std::move(net_names);
    e.cont_assign_targets_ = std::move(cont_assign_targets);
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
    e.alias_pairs_ = std::move(alias_pairs);
    e.alias_bit_pairs_ = std::move(alias_bit_pairs);
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
    e.task_names_ = std::move(task_names);
    e.let_names_ = std::move(let_names);
    e.sequence_names_ = std::move(sequence_names);
    e.property_registry_ = std::move(property_registry);
    e.func_decls_ = std::move(func_decls);
    RestoreScopeMaps(e);
  }
};

// §23.9/§24.3: the enclosing-scope chain follows lexical nesting, not the
// instance tree. A lexically nested declaration (set up by the nested-decl
// elaboration site, which records the enclosing scope in `pending`) extends
// the caller's chain by one entry; any other call (a separately-instantiated
// child, a bind, or the top cell) starts from an empty chain so the prior
// caller's scope does not leak in. Answers the caller's chain, put back once
// the cell is done. Moved out of ElaborateModule, which c70321083's guard took
// past readability-function-size's statement threshold.
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

// §14.14: this cell's own global clocking declaration `own_gclk` joins the
// chain of its ancestors' rather than replacing it, so back() is the
// declaration closest to the point of reference -- rule a) before rule b) --
// and the answer is the event a $global_clock reference in the cell resolves
// to, null where the chain is empty. The caller pops its own entry once the
// cell is done.
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
  auto* mod = arena_.Create<RtlirModule>();
  InitRtlirModuleHeader(mod, decl, unit_, diag_);

  // The per-module item-elaboration state (the members reset by
  // ResetItemElaborationState) is accumulated as this module's items are
  // elaborated and is read by the deferred post-item validations. Elaborating a
  // child instance recurses back into ElaborateModule, which resets and
  // repopulates those members for the child; without restoring them the
  // parent's validations would run against the child's leftover state -- for
  // example a child's continuous assign to a port named like a parent signal
  // would be misread as a multiple-driver conflict (§23.3.3). Snapshot the
  // state here and restore it before returning so each ElaborateModule call is
  // transparent to its caller. (nested_module_decls_ already had a narrower
  // per-call save at the instance site; this generalizes it to the full set.)
  ItemElaborationStateSaver saved_item_state(*this);

  std::vector<std::unordered_set<std::string_view>> saved_enclosing =
      EnterEnclosingScopeChain(enclosing_scope_names_, pending_enclosing_scope_,
                               has_pending_enclosing_scope_);
  // §16.15: the default disable iff a nested declaration inherits from the
  // scope it is declared in, taken here so that the instances this cell
  // contains, other than its own nested declarations, inherit none.
  inherited_default_disable_iff_ = nested_default_disable_iff_;
  nested_default_disable_iff_ = nullptr;

  // While this cell is elaborated it is the parent of any instances it
  // contains; record its library so child binding can fall back to it
  // (§33.4.1.5) or inherit it for a library-less use clause (§33.4.1.6). The
  // previous value is restored before returning.
  std::string saved_library = std::move(current_library_);
  current_library_.assign(decl->library.data(), decl->library.size());

  ApplyCompilationUnitImports(mod);
  ApplyHeaderImports(decl);
  ImportedEnumCtx enum_ctx{unit_, arena_, typedefs_, enum_member_names_};
  RegisterImportedEnumLiterals(decl, mod, enum_ctx);
  RegisterCuEnumLiterals(decl, mod, enum_ctx);

  ElaborateParamPortList(decl, params, mod);

  // §23.10 (printed page 763) with §6.20.1 (printed 125): a module declared
  // with no parameter port list declares its value parameters among its
  // items, and the instantiation's assignments override them there. They are
  // installed for the items below, with the instantiating module's parameters
  // -- registered from the item loop this instantiation is an item of, until
  // ElaborateItems registers this module's own -- as the scope their
  // expressions stand in. A module with a parameter port list has its body
  // parameters as localparams, which no assignment reaches, so none are
  // installed for it. ElaborateParamPortList alone read the assignments
  // before, so `c #(.P(5)) u()` over `module c; parameter P = 1;` kept 1.
  const InstanceParamAssignments kBodyAssignments{params,
                                                  RegisteredModuleScope()};
  BodyParamAssignmentsGuard body_assignments_guard(
      decl->has_param_port_list ? nullptr : &kBodyAssignments);

  ReportParamsMissingValue(decl, mod, diag_);

  ElaboratePorts(decl, mod);

  CheckConditionalGenerateNaming(decl);
  AssignGenerateBlockNames(decl);

  // §14.14 (rule b): a $global_clock reference resolves against the effective
  // global clocking found by searching up the instance hierarchy. Extend the
  // in-scope flag with this cell's own declaration before its items -- and the
  // child instances among them -- are elaborated, so a reference in a module
  // that does not itself declare a global clocking still resolves against an
  // ancestor's. Restored below so the flag reflects the parent's chain again.
  bool saved_global_clocking_in_scope = global_clocking_in_scope_;
  global_clocking_in_scope_ =
      saved_global_clocking_in_scope || ModuleDeclaresGlobalClocking(decl);

  const std::vector<EventExpr>* own_gclk = ModuleGlobalClockingEvent(decl);
  const std::vector<EventExpr>* saved_global_clocking_event =
      module_global_clocking_event_;
  module_global_clocking_event_ = EnterGlobalClockingChain(
      global_clocking_scopes_, own_gclk, current_inst_path_, arena_);

  ElaborateItems(decl, mod);
  ResolveExplicitPortTypes(decl, mod);
  module_global_clocking_event_ = saved_global_clocking_event;
  if (own_gclk != nullptr) global_clocking_scopes_.pop_back();
  global_clocking_in_scope_ = saved_global_clocking_in_scope;
  current_library_ = std::move(saved_library);
  enclosing_scope_names_ = std::move(saved_enclosing);
  // declared_names_ holds this module's complete set of declared names at this
  // point, and the Restore below takes it back to what the caller had. The
  // generate constructs this module queued are elaborated after that, by
  // Elaborator::ProcessPendingGenerate, and §23.9 judges what they declare
  // against the scope they were written in, so keep the set here for them.
  module_declared_names_[mod] = declared_names_;
  saved_item_state.Restore(*this);
  return mod;
}

}  // namespace delta
