#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <format>
#include <optional>
#include <unordered_map>
#include <unordered_set>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

static std::optional<int64_t> FindParamOverride(
    const Elaborator::ParamList& params, std::string_view name) {
  for (const auto& [oname, oval] : params) {
    if (oname == name) {
      return oval;
    }
  }
  return std::nullopt;
}

// §6.20.3: follow typedef and type-parameter substitutions to decide whether a
// declared type ultimately names a class type.
static bool ParamTypeResolvesToClass(
    const DataType& dtype, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names) {
  const DataType* cur = &dtype;
  for (int depth = 0; depth < 32 && cur->kind == DataTypeKind::kNamed;
       ++depth) {
    if (class_names.count(cur->type_name) > 0) return true;
    auto it = typedefs.find(cur->type_name);
    if (it == typedefs.end()) break;
    cur = &it->second;
  }
  return false;
}

// The elaborator state needed to validate a type-parameter-typed value
// parameter's assigned value, bundled to stay within the argument-count limit.
struct TypeParamValueCtx {
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& class_names;
  DiagEngine& diag;
};

// §6.20.3: a value parameter whose declared type is one of this module's type
// parameters, and which (after the instance override or default) resolved to a
// class type, cannot be assigned an integral constant value.
static void CheckTypeParamValueAssignable(const ModuleDecl* decl, size_t i,
                                          const Expr* pval,
                                          const ScopeMap& scope,
                                          const TypeParamValueCtx& ctx) {
  if (i >= decl->param_types.size()) return;
  const DataType& dt = decl->param_types[i];
  if (dt.kind != DataTypeKind::kNamed) return;
  if (decl->type_param_names.count(dt.type_name) == 0) return;
  if (!pval || !ConstEvalInt(pval, scope)) return;
  if (!ParamTypeResolvesToClass(dt, ctx.typedefs, ctx.class_names)) return;
  ctx.diag.Error(pval->range.start,
                 std::format("cannot assign an integral value to parameter "
                             "whose type parameter '{}' resolved to a class "
                             "type",
                             dt.type_name));
}

bool Elaborator::HasParamPortWithoutDefault(const ModuleDecl* decl) {
  for (const auto& [name, expr] : decl->params) {
    if (decl->localparam_port_names.count(name)) continue;
    if (decl->type_param_names.count(name)) continue;
    if (expr == nullptr) return true;
  }
  return false;
}

void PopulateParamTypeInfo(RtlirParamDecl& pd, const DataType& dtype) {
  pd.has_decl_range = dtype.packed_dim_left != nullptr;
  pd.has_decl_type = dtype.kind != DataTypeKind::kImplicit || dtype.is_signed;
  pd.decl_is_signed = dtype.is_signed;
  pd.decl_type_implicit = dtype.kind == DataTypeKind::kImplicit;
  if (pd.has_decl_range || pd.has_decl_type) {
    pd.decl_width = EvalTypeWidth(dtype);
  }
}

void PopulateParamTypeInfo(RtlirParamDecl& pd, const DataType& dtype,
                           const TypedefMap& typedefs, const ScopeMap& scope) {
  pd.has_decl_range = dtype.packed_dim_left != nullptr;
  pd.has_decl_type = dtype.kind != DataTypeKind::kImplicit || dtype.is_signed;
  pd.decl_is_signed = dtype.is_signed;
  pd.decl_type_implicit = dtype.kind == DataTypeKind::kImplicit;
  if (pd.has_decl_range || pd.has_decl_type) {
    pd.decl_width = EvalTypeWidth(dtype, typedefs, scope);
  }
}

bool ParamExpectsIntegerValue(const RtlirParamDecl& pd, const DataType& dtype) {
  // §6.20.2: a value parameter is in an integer context — and so subject to the
  // real-to-integer conversion of §6.12.1 — when it carries a packed range or
  // an explicit non-real data type. A bare (untyped) parameter or one declared
  // real takes a real value instead and is not converted here.
  return pd.has_decl_range || (pd.has_decl_type && !IsRealType(dtype.kind));
}

int64_t ConvertOverrideValue(int64_t value, const RtlirParamDecl& pd) {
  // §6.20.2: a parameter declared with an explicit range, or with an explicit
  // (non-implicit) data type, keeps the sign and range of its declaration; a
  // value override does not change them, so the incoming value is coerced into
  // the declared width. A parameter with no range and only an implicit type
  // (including a bare `signed`) instead takes its range from the final value
  // assigned, so the override value passes through unchanged.
  bool has_fixed_width =
      pd.has_decl_range || (pd.has_decl_type && !pd.decl_type_implicit);
  if (!has_fixed_width) return value;
  uint32_t w = pd.decl_width;
  if (w == 0 || w >= 64) return value;
  uint64_t mask = (uint64_t{1} << w) - 1;
  uint64_t masked = static_cast<uint64_t>(value) & mask;
  if (pd.decl_is_signed) {
    uint64_t sign_bit = uint64_t{1} << (w - 1);
    if (masked & sign_bit) masked |= ~mask;
  }
  return static_cast<int64_t>(masked);
}

// Register a single imported package item into a module's elaboration scopes:
// typedefs become available by name, and const parameters are folded into the
// compilation-unit parameter scope. Shared by the wildcard and named-import
// branches of ApplyHeaderImports.
static void RegisterHeaderImportItem(const ModuleItem* pi,
                                     std::string_view name,
                                     TypedefMap& typedefs,
                                     ScopeMap& cu_param_scope) {
  if (pi->kind == ModuleItemKind::kTypedef) {
    typedefs[name] = pi->typedef_type;
  } else if (pi->kind == ModuleItemKind::kParamDecl && pi->init_expr) {
    auto val = ConstEvalInt(pi->init_expr, cu_param_scope);
    if (val) cu_param_scope[name] = *val;
  }
}

// Locate a package declaration by name within the compilation unit, or nullptr.
static const PackageDecl* FindPackageByName(const CompilationUnit* unit,
                                            std::string_view pkg_name) {
  for (const auto* p : unit->packages) {
    if (p->name == pkg_name) return p;
  }
  return nullptr;
}

// Register every named item of a wildcard-imported package.
static void RegisterWildcardHeaderImport(const PackageDecl* pkg,
                                         TypedefMap& typedefs,
                                         ScopeMap& cu_param_scope) {
  for (const auto* pi : pkg->items) {
    if (!pi->name.empty())
      RegisterHeaderImportItem(pi, pi->name, typedefs, cu_param_scope);
  }
}

// Register a single named item of an explicitly-named package import.
static void RegisterNamedHeaderImport(const PackageDecl* pkg,
                                      std::string_view target,
                                      TypedefMap& typedefs,
                                      ScopeMap& cu_param_scope) {
  for (const auto* pi : pkg->items) {
    if (pi->name == target) {
      RegisterHeaderImportItem(pi, target, typedefs, cu_param_scope);
      break;
    }
  }
}

// Apply one header (package) import directive, resolving the named package and
// registering either all of its items (wildcard) or a single named item.
static void ApplyHeaderImport(const ImportItem& import_item,
                              const CompilationUnit* unit, TypedefMap& typedefs,
                              ScopeMap& cu_param_scope) {
  const PackageDecl* pkg = FindPackageByName(unit, import_item.package_name);
  if (!pkg) return;
  if (import_item.is_wildcard) {
    RegisterWildcardHeaderImport(pkg, typedefs, cu_param_scope);
  } else {
    RegisterNamedHeaderImport(pkg, import_item.item_name, typedefs,
                              cu_param_scope);
  }
}

void Elaborator::ApplyHeaderImports(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    if (!item->import_item.is_header) continue;
    ApplyHeaderImport(item->import_item, unit_, typedefs_, cu_param_scope_);
  }
}

// §23.2.2.3: an explicitly named port (.name(expr)) takes the self-determined
// data type of its connection expression. Resolve the expression's width
// against the module's already-elaborated variables and nets. Returns 0 when
// the width cannot be determined here, leaving the port's default untouched.
static uint32_t ExplicitPortExprWidth(const Expr* expr,
                                      const RtlirModule* mod) {
  if (!expr) return 0;
  switch (expr->kind) {
    case ExprKind::kIdentifier:
      for (const auto& v : mod->variables)
        if (v.name == expr->text) return v.width;
      for (const auto& n : mod->nets)
        if (n.name == expr->text) return n.width;
      return 0;
    case ExprKind::kConcatenation: {
      uint32_t total = 0;
      for (const auto* el : expr->elements)
        total += ExplicitPortExprWidth(el, mod);
      return total;
    }
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

// Resolve the value of a parameter that has a default expression (pval) but no
// instantiation override. Handles the §6.20.7 unbounded-parameter forms and the
// §6.20.2 integer/real constant folding. refers_to_unbounded and
// contains_dollar are precomputed by the caller because they require Elaborator
// member helpers; has_param_type / param_type describe the optional declared
// data type.
// §6.20.7: an unbounded ($) parameter value, or a reference to another
// unbounded parameter, makes this parameter unbounded too. Returns true when
// the value was recognized as unbounded (and pd updated), so the caller can
// stop.
static bool TryResolveUnboundedParamValue(RtlirParamDecl& pd, const Expr* pval,
                                          bool refers_to_unbounded) {
  if (pval->kind == ExprKind::kIdentifier && pval->text == "$") {
    pd.is_unbounded = true;
    return true;
  }
  if (pval->kind == ExprKind::kIdentifier && refers_to_unbounded) {
    // §6.20.7: assigning a $ (unbounded) parameter to another parameter is
    // legal; the assigned-to parameter is itself unbounded.
    pd.is_unbounded = true;
    return true;
  }
  return false;
}

// Fold a parameter's default expression into a concrete value: prefer an
// integer constant, then (for integer-typed parameters) a real constant rounded
// per §6.12.1.
static void FoldParamConstantValue(RtlirParamDecl& pd, const Expr* pval,
                                   const ScopeMap& scope, bool has_param_type,
                                   const DataType* param_type) {
  auto val = ConstEvalInt(pval, scope);
  if (val) {
    pd.resolved_value = *val;
    pd.is_resolved = true;
  } else if (!pd.is_type_param && has_param_type &&
             ParamExpectsIntegerValue(pd, *param_type)) {
    // §6.20.2: an integer-typed parameter set from a real constant is
    // converted to an integer per §6.12.1 (round to nearest, ties away
    // from zero).
    if (auto rval = ConstEvalReal(pval, scope)) {
      pd.resolved_value = std::llround(*rval);
      pd.is_resolved = true;
    }
  }
}

// §6.20: a parameter's default value expression together with the
// classification of that expression and the parameter's declared type. These
// fields describe a single domain object - the value being assigned to the
// parameter - so they are bundled and passed together when resolving the
// parameter's concrete value.
struct ParamValueExpr {
  const Expr* pval;          // the default value expression
  std::string_view pname;    // name of the parameter receiving the value
  bool refers_to_unbounded;  // §6.20.7: expr is an unbounded ($) parameter ref
  bool contains_dollar;      // §6.20.7: expr contains a $ subexpression
  bool has_param_type;       // parameter has an explicit declared data type
  const DataType* param_type;  // §6.20.2: that declared type (null if none)
};

static void ResolveUnresolvedParamValue(RtlirParamDecl& pd,
                                        const ParamValueExpr& val,
                                        const ScopeMap& scope,
                                        DiagEngine& diag) {
  if (TryResolveUnboundedParamValue(pd, val.pval, val.refers_to_unbounded)) {
    return;
  }
  if (val.contains_dollar) {
    // §6.20.7: $ must be the entire, self-contained parameter value; it
    // may not be combined with operators or selects in this context.
    diag.Error(val.pval->range.start,
               std::format("'$' may only be assigned to parameter '{}' "
                           "as a complete, self-contained expression",
                           val.pname));
  }
  FoldParamConstantValue(pd, val.pval, scope, val.has_param_type,
                         val.param_type);
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
                           pd.name, decl->name));
  }
}

// Apply an instantiation override (if any) to a parameter, coercing the value
// to the declared width per §6.20.2. Returns true when an override was applied.
static bool ApplyParamOverride(RtlirParamDecl& pd,
                               const Elaborator::ParamList& params,
                               std::string_view pname) {
  auto override_val = FindParamOverride(params, pname);
  if (!override_val) return false;
  pd.resolved_value = ConvertOverrideValue(*override_val, pd);
  pd.is_resolved = true;
  pd.from_override = true;
  return true;
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
  mod->delay_mode = unit->delay_mode_directive;
  mod->attrs = ResolveAttributes(decl->attrs, diag);

  RtlirImport std_import;
  std_import.package_name = "std";
  std_import.is_wildcard = true;
  mod->imports.push_back(std_import);
}

// Build the non-value identity/type fields of a parameter declaration (name,
// localparam/type-param flags, declared-type info). Value resolution is handled
// separately because it requires Elaborator member helpers.
static RtlirParamDecl BuildParamDeclShell(const ModuleDecl* decl, size_t i,
                                          const TypedefMap& typedefs,
                                          const ScopeMap& scope,
                                          bool has_param_type) {
  const auto& [pname, pval] = decl->params[i];
  RtlirParamDecl pd;
  pd.name = pname;
  pd.default_value = pval;
  pd.is_resolved = false;
  pd.is_type_param = decl->type_param_names.count(pname) > 0;
  pd.is_localparam = decl->localparam_port_names.count(pname) > 0;
  if (has_param_type) {
    PopulateParamTypeInfo(pd, decl->param_types[i], typedefs, scope);
  }
  return pd;
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
  specparam_names_.clear();
  enum_var_names_.clear();
  enum_member_names_.clear();
  const_names_.clear();
  const_var_names_.clear();
  class_var_names_.clear();
  class_var_types_.clear();
  var_init_names_.clear();
  output_port_targets_.clear();
  nettype_net_names_.clear();
  interconnect_names_.clear();
  scalar_var_names_.clear();
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
// Elaborator::ResetItemElaborationState exactly; decltype is used so the field
// types track the members without naming the elaborator's private nested types.
struct ItemElaborationStateSaver {
  decltype(Elaborator::forward_typedef_kinds_) forward_typedef_kinds;
  decltype(Elaborator::declared_names_) declared_names;
  decltype(Elaborator::net_names_) net_names;
  decltype(Elaborator::cont_assign_targets_) cont_assign_targets;
  decltype(Elaborator::proc_assign_targets_) proc_assign_targets;
  decltype(Elaborator::var_types_) var_types;
  decltype(Elaborator::var_array_info_) var_array_info;
  decltype(Elaborator::specparam_names_) specparam_names;
  decltype(Elaborator::enum_var_names_) enum_var_names;
  decltype(Elaborator::enum_member_names_) enum_member_names;
  decltype(Elaborator::const_names_) const_names;
  decltype(Elaborator::const_var_names_) const_var_names;
  decltype(Elaborator::class_var_names_) class_var_names;
  decltype(Elaborator::class_var_types_) class_var_types;
  decltype(Elaborator::var_init_names_) var_init_names;
  decltype(Elaborator::output_port_targets_) output_port_targets;
  decltype(Elaborator::nettype_net_names_) nettype_net_names;
  decltype(Elaborator::interconnect_names_) interconnect_names;
  decltype(Elaborator::scalar_var_names_) scalar_var_names;
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
  decltype(Elaborator::func_decls_) func_decls;

  explicit ItemElaborationStateSaver(Elaborator& e) {
    forward_typedef_kinds = std::move(e.forward_typedef_kinds_);
    declared_names = std::move(e.declared_names_);
    net_names = std::move(e.net_names_);
    cont_assign_targets = std::move(e.cont_assign_targets_);
    proc_assign_targets = std::move(e.proc_assign_targets_);
    var_types = std::move(e.var_types_);
    var_array_info = std::move(e.var_array_info_);
    specparam_names = std::move(e.specparam_names_);
    enum_var_names = std::move(e.enum_var_names_);
    enum_member_names = std::move(e.enum_member_names_);
    const_names = std::move(e.const_names_);
    const_var_names = std::move(e.const_var_names_);
    class_var_names = std::move(e.class_var_names_);
    class_var_types = std::move(e.class_var_types_);
    var_init_names = std::move(e.var_init_names_);
    output_port_targets = std::move(e.output_port_targets_);
    nettype_net_names = std::move(e.nettype_net_names_);
    interconnect_names = std::move(e.interconnect_names_);
    scalar_var_names = std::move(e.scalar_var_names_);
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
    func_decls = std::move(e.func_decls_);
    e.ResetItemElaborationState();
  }

  void Restore(Elaborator& e) {
    e.forward_typedef_kinds_ = std::move(forward_typedef_kinds);
    e.declared_names_ = std::move(declared_names);
    e.net_names_ = std::move(net_names);
    e.cont_assign_targets_ = std::move(cont_assign_targets);
    e.proc_assign_targets_ = std::move(proc_assign_targets);
    e.var_types_ = std::move(var_types);
    e.var_array_info_ = std::move(var_array_info);
    e.specparam_names_ = std::move(specparam_names);
    e.enum_var_names_ = std::move(enum_var_names);
    e.enum_member_names_ = std::move(enum_member_names);
    e.const_names_ = std::move(const_names);
    e.const_var_names_ = std::move(const_var_names);
    e.class_var_names_ = std::move(class_var_names);
    e.class_var_types_ = std::move(class_var_types);
    e.var_init_names_ = std::move(var_init_names);
    e.output_port_targets_ = std::move(output_port_targets);
    e.nettype_net_names_ = std::move(nettype_net_names);
    e.interconnect_names_ = std::move(interconnect_names);
    e.scalar_var_names_ = std::move(scalar_var_names);
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
    e.func_decls_ = std::move(func_decls);
  }
};

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

  // §23.9/§24.3: the enclosing-scope chain follows lexical nesting, not the
  // instance tree. A lexically nested declaration (set up by the nested-decl
  // elaboration site, which records the enclosing scope in
  // pending_enclosing_scope_) extends the caller's chain by one entry; any
  // other call (a separately-instantiated child, a bind, or the top cell)
  // starts from an empty chain so the prior caller's scope does not leak in.
  std::vector<std::unordered_set<std::string_view>> saved_enclosing =
      std::move(enclosing_scope_names_);
  enclosing_scope_names_.clear();
  if (has_pending_enclosing_scope_) {
    enclosing_scope_names_ = saved_enclosing;
    enclosing_scope_names_.push_back(std::move(pending_enclosing_scope_));
    pending_enclosing_scope_.clear();
    has_pending_enclosing_scope_ = false;
  }

  // While this cell is elaborated it is the parent of any instances it
  // contains; record its library so child binding can fall back to it
  // (§33.4.1.5) or inherit it for a library-less use clause (§33.4.1.6). The
  // previous value is restored before returning.
  std::string saved_library = std::move(current_library_);
  current_library_.assign(decl->library.data(), decl->library.size());

  ApplyHeaderImports(decl);
  ImportedEnumCtx enum_ctx{unit_, arena_, typedefs_, enum_member_names_};
  RegisterImportedEnumLiterals(decl, mod, enum_ctx);

  TypeParamValueCtx tp_ctx{typedefs_, class_names_, diag_};
  for (size_t i = 0; i < decl->params.size(); ++i) {
    const auto& [pname, pval] = decl->params[i];
    auto scope = BuildParamScope(mod);
    bool has_param_type = i < decl->param_types.size() &&
                          decl->type_param_names.count(pname) == 0;
    RtlirParamDecl pd =
        BuildParamDeclShell(decl, i, typedefs_, scope, has_param_type);
    ApplyParamOverride(pd, params, pname);
    if (!pd.is_resolved && pval) {
      const DataType* param_type =
          has_param_type ? &decl->param_types[i] : nullptr;
      bool refers_to_unbounded = pval->kind == ExprKind::kIdentifier &&
                                 RefersToUnboundedParam(mod, pval->text);
      bool contains_dollar = ContainsDollarSubexpr(pval);
      ParamValueExpr val{
          pval,           pname,     refers_to_unbounded, contains_dollar,
          has_param_type, param_type};
      ResolveUnresolvedParamValue(pd, val, scope, diag_);
    }
    CheckTypeParamValueAssignable(decl, i, pval, scope, tp_ctx);
    mod->params.push_back(pd);
  }

  ReportParamsMissingValue(decl, mod, diag_);

  ElaboratePorts(decl, mod);

  CheckConditionalGenerateNaming(decl);
  AssignGenerateBlockNames(decl);
  ElaborateItems(decl, mod);
  ResolveExplicitPortTypes(decl, mod);
  current_library_ = std::move(saved_library);
  enclosing_scope_names_ = std::move(saved_enclosing);
  saved_item_state.Restore(*this);
  return mod;
}

// Diagnose repeated explicitly-named (.name) ports within a single non-ANSI
// header.
static void CheckDuplicateExplicitPortNames(const ModuleDecl* decl,
                                            DiagEngine& diag) {
  std::unordered_set<std::string_view> explicit_names;
  for (const auto& port : decl->ports) {
    if (port.is_explicit_named && !port.name.empty()) {
      if (!explicit_names.insert(port.name).second) {
        diag.Error(port.loc,
                   std::format("duplicate port name '.{}'", port.name));
      }
    }
  }
}

// Diagnose repeated ordinary port names in an ANSI header, tracked across the
// run via ansi_port_names.
static void CheckDuplicateAnsiPortNames(
    const ModuleDecl* decl,
    std::unordered_set<std::string_view>& ansi_port_names, DiagEngine& diag) {
  for (const auto& port : decl->ports) {
    if (!port.name.empty()) {
      if (!ansi_port_names.insert(port.name).second) {
        diag.Error(port.loc,
                   std::format("duplicate port name '{}'", port.name));
      }
    }
  }
}

// Diagnose repeated port names: explicitly named (.name) ports in a non-ANSI
// header, and ordinary port names in an ANSI header (tracked across the run via
// ansi_port_names).
static void CheckDuplicatePortNames(
    const ModuleDecl* decl,
    std::unordered_set<std::string_view>& ansi_port_names, DiagEngine& diag) {
  if (decl->is_non_ansi_ports) {
    CheckDuplicateExplicitPortNames(decl, diag);
  } else {
    CheckDuplicateAnsiPortNames(decl, ansi_port_names, diag);
  }
}

// §23.2.2: validate the contexts in which a port default value may appear —
// input ports only, ANSI-style declarations only, and singular non-interconnect
// types only.
static void ValidatePortDefaultValue(const PortDecl& port, bool is_non_ansi,
                                     DiagEngine& diag) {
  if (port.direction != Direction::kInput) {
    diag.Error(port.loc,
               std::format("default value on {} port '{}'; defaults are "
                           "only allowed on input ports",
                           port.direction == Direction::kOutput  ? "output"
                           : port.direction == Direction::kInout ? "inout"
                                                                 : "ref",
                           port.name));
  }
  if (is_non_ansi) {
    diag.Error(port.loc, std::format("default value on port '{}'; defaults are "
                                     "only allowed with ANSI-style port "
                                     "declarations",
                                     port.name));
  }
  if (port.data_type.is_interconnect) {
    diag.Error(port.loc, std::format("default value on interconnect port '{}'",
                                     port.name));
  }
  if (!port.unpacked_dims.empty() || !IsSingularType(port.data_type)) {
    diag.Error(port.loc, std::format("default value on non-singular port '{}'",
                                     port.name));
  }
}

// Fold each unpacked-dimension expression of a port into a concrete size,
// supporting both [msb:lsb] ranges and single-size [n] forms.
static void ComputePortUnpackedDimSizes(const PortDecl& port, RtlirPort& rp) {
  for (auto* dim : port.unpacked_dims) {
    if (!dim) continue;
    if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
      auto lv = ConstEvalInt(dim->lhs);
      auto rv = ConstEvalInt(dim->rhs);
      if (lv && rv) {
        rp.unpacked_dim_sizes.push_back(
            static_cast<uint32_t>(std::abs(*lv - *rv) + 1));
      }
    } else {
      auto sv = ConstEvalInt(dim);
      if (sv && *sv > 0)
        rp.unpacked_dim_sizes.push_back(static_cast<uint32_t>(*sv));
    }
  }
  rp.num_unpacked_dims = static_cast<uint32_t>(rp.unpacked_dim_sizes.size());
}

// Reject port types that may never appear on a port (chandle, virtual
// interface). Emits the diagnostic and returns true when the port must be
// skipped.
static bool RejectIllegalPortType(const PortDecl& port, DiagEngine& diag) {
  if (port.data_type.kind == DataTypeKind::kChandle) {
    diag.Error(port.loc, "chandle cannot be used as a port type");
    return true;
  }
  if (port.data_type.kind == DataTypeKind::kVirtualInterface) {
    diag.Error(port.loc, "virtual interface cannot be used as a port type");
    return true;
  }
  return false;
}

// §23.2.2: diagnose a non-ANSI port that appears in the header but never gets a
// direction declaration in the module body.
static void DiagnoseMissingNonAnsiPortDirection(const PortDecl& port,
                                                bool is_non_ansi,
                                                DiagEngine& diag) {
  if (is_non_ansi && !port.name.empty() && !port.is_explicit_named &&
      port.direction == Direction::kNone) {
    diag.Error(port.loc,
               std::format("port '{}' has no direction declaration in the "
                           "module body",
                           port.name));
  }
}

// §23.2.2.1: validate the per-port type constraints that do not block building
// the RtlirPort: interconnect ports may not be signed, and inout ports may not
// carry a variable data type.
static void DiagnosePortTypeConstraints(const PortDecl& port, bool port_is_var,
                                        DiagEngine& diag) {
  // Interconnect is an untyped generic connection, so it carries no signedness
  // of its own.
  if (port.data_type.is_interconnect && port.data_type.is_signed) {
    diag.Error(port.loc,
               std::format("interconnect port '{}' shall not be declared "
                           "signed",
                           port.name));
  }
  if (port.direction == Direction::kInout && port_is_var) {
    diag.Error(port.loc, std::format("variable data type is not permitted on "
                                     "inout port '{}'",
                                     port.name));
  }
}

// State threaded into ElaborateOnePort that would otherwise be Elaborator
// members; grouped so the helper can stay a free function (no header change).
// The non-ANSI port-tracking sets and the type-lookup context together form the
// elaboration state for one module's port list, so they travel as one object.
struct PortElabContext {
  const TypedefMap& typedefs;
  const ScopeMap& param_scope;
  std::unordered_set<std::string_view>& complete_ports;
  std::unordered_map<std::string_view, uint32_t>& partial_ports;
  std::unordered_set<std::string_view>& signed_ports;
  DiagEngine& diag;
};

// Record the type information of a directioned non-ANSI port so the matching
// body net/variable declaration can be reconciled later (§23.2.2.1). The
// tracking sets are reference members of the context, so a const reference
// still allows recording into them.
static void TrackNonAnsiPortType(const ModuleDecl* decl, const PortDecl& port,
                                 const PortElabContext& ctx) {
  if (!decl->is_non_ansi_ports || port.name.empty() ||
      port.direction == Direction::kNone) {
    return;
  }
  if (port.data_type.kind != DataTypeKind::kImplicit) {
    ctx.complete_ports.insert(port.name);
  } else {
    ctx.partial_ports[port.name] =
        EvalTypeWidth(port.data_type, ctx.typedefs, ctx.param_scope);
    // §23.2.2.1: remember a `signed` port direction declaration so the
    // matching net/variable declaration can be considered signed too.
    if (port.data_type.is_signed) ctx.signed_ports.insert(port.name);
  }
}

// Fill the base (non-interface) fields of an RtlirPort from its declaration,
// including the folded unpacked-dimension sizes.
static RtlirPort BuildRtlirPortBase(const PortDecl& port, bool port_is_var,
                                    uint32_t width) {
  RtlirPort rp;
  rp.name = port.name;
  rp.direction = port.direction;
  rp.type_kind = port.data_type.kind;
  rp.width = width;
  rp.is_signed = port.data_type.is_signed;
  rp.is_var = port_is_var;
  rp.is_interconnect = port.data_type.is_interconnect;
  rp.default_value = port.default_value;
  ComputePortUnpackedDimSizes(port, rp);
  return rp;
}

// Elaborate one port declaration into its RtlirPort: run the per-port
// diagnostics, track non-ANSI type info, and build the base fields. The
// interface-port flag is resolved by the caller because it needs FindModule.
static RtlirPort ElaborateOnePort(const ModuleDecl* decl, const PortDecl& port,
                                  PortElabContext& ctx) {
  DiagnoseMissingNonAnsiPortDirection(port, decl->is_non_ansi_ports, ctx.diag);
  TrackNonAnsiPortType(decl, port, ctx);

  if (port.default_value) {
    ValidatePortDefaultValue(port, decl->is_non_ansi_ports, ctx.diag);
  }

  bool port_is_var = !port.data_type.is_net && !port.data_type.is_interconnect;
  DiagnosePortTypeConstraints(port, port_is_var, ctx.diag);

  uint32_t width = EvalTypeWidth(port.data_type, ctx.typedefs, ctx.param_scope);
  return BuildRtlirPortBase(port, port_is_var, width);
}

// 23.2.2.4: a default input-port value is a constant expression evaluated in
// the scope of the module where the port is defined, not in the scope of the
// instantiating module. Fold it against this module's parameter scope (which
// already includes the compilation-unit scope and any per-instance parameter
// overrides) and capture the resolved constant as a literal, so it is not
// re-resolved in the instantiating scope when later used as a port connection.
static void FoldPortDefaultValue(Arena& arena, const ScopeMap& scope,
                                 RtlirPort& rp) {
  if (rp.default_value == nullptr) return;
  // A literal default is already scope-independent, so leave it untouched; this
  // also avoids truncating a wide (>64-bit) literal through the 64-bit fold.
  // Only name-bearing expressions need to be pinned to the defining scope.
  if (rp.default_value->kind == ExprKind::kIntegerLiteral) return;
  auto v = ConstEvalInt(rp.default_value, scope);
  if (!v) return;
  auto* lit = arena.Create<Expr>();
  lit->kind = ExprKind::kIntegerLiteral;
  lit->int_val = static_cast<uint64_t>(*v);
  rp.default_value = lit;
}

void Elaborator::ElaboratePorts(const ModuleDecl* decl, RtlirModule* mod) {
  auto param_scope = BuildParamScope(mod);

  CheckDuplicatePortNames(decl, ansi_port_names_, diag_);

  PortElabContext ctx{typedefs_,
                      param_scope,
                      non_ansi_complete_ports_,
                      non_ansi_partial_ports_,
                      non_ansi_signed_ports_,
                      diag_};

  for (const auto& port : decl->ports) {
    if (RejectIllegalPortType(port, diag_)) continue;

    RtlirPort rp = ElaborateOnePort(decl, port, ctx);
    FoldPortDefaultValue(arena_, param_scope, rp);

    if (port.is_interface_port) {
      rp.is_interface_port = true;
      // §23.3.3.4: a named interface-type port (`bus_if p` / `bus_if.mp p`)
      // records its required interface type so the connection check can reject
      // an instance of a different type. A generic `interface p` port leaves
      // type_name empty, so it keeps accepting any interface instance.
      rp.interface_type_name = port.data_type.type_name;
    } else if (port.direction == Direction::kNone &&
               port.data_type.kind == DataTypeKind::kNamed &&
               !port.data_type.type_name.empty()) {
      auto* ifc_decl = FindModule(port.data_type.type_name);
      if (ifc_decl && ifc_decl->decl_kind == ModuleDeclKind::kInterface) {
        rp.is_interface_port = true;
        rp.interface_type_name = port.data_type.type_name;
      }
    }

    mod->ports.push_back(rp);
  }
}

}  // namespace delta
