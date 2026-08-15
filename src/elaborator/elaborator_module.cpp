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

// §23.10.3: a value parameter whose declared type is one of this module's type
// parameters, and which (after the instance override or default) resolved to a
// class type, cannot be assigned an integral constant value. §23.10.3 states
// the rule on this very construct -- "if the type parameter T is not overridden
// to an integral type, the evaluation of the default value for parameter p is
// illegal" -- while §6.20.2 states only general assignment compatibility.
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
                             dt.type_name),
                 Subclause("23.10.3"));
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

void RecordParamDeclRange(RtlirParamDecl& pd, const DataType& dtype,
                          const ScopeMap& scope) {
  if (!dtype.packed_dim_left || !dtype.packed_dim_right) return;
  auto left = ConstEvalInt(dtype.packed_dim_left, scope);
  auto right = ConstEvalInt(dtype.packed_dim_right, scope);
  if (!left || !right) return;
  pd.decl_range_left = *left;
  pd.decl_range_right = *right;
  pd.has_decl_range_bounds = true;
}

bool ParamExpectsIntegerValue(const RtlirParamDecl& pd, const DataType& dtype) {
  // §6.20.2: a value parameter is in an integer context — and so subject to the
  // real-to-integer conversion of §6.12.1 — when it carries a packed range or
  // an explicit non-real data type. A bare (untyped) parameter or one declared
  // real takes a real value instead and is not converted here.
  return pd.has_decl_range || (pd.has_decl_type && !IsRealType(dtype.kind));
}

bool TryFoldRealParamValue(RtlirParamDecl& pd, const Expr* init,
                           const DataType& dtype, const ScopeMap& scope) {
  if (!IsRealType(dtype.kind)) return false;
  auto rval = ConstEvalReal(init, scope);
  if (!rval) return false;
  pd.resolved_real = *rval;
  pd.is_real_value = true;
  pd.is_resolved = true;
  return true;
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
// branches of ApplyImport.
static void RegisterImportItem(const ModuleItem* pi, std::string_view name,
                               TypedefMap& typedefs, ScopeMap& cu_param_scope) {
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
static void RegisterWildcardImport(const PackageDecl* pkg, TypedefMap& typedefs,
                                   ScopeMap& cu_param_scope) {
  for (const auto* pi : pkg->items) {
    if (!pi->name.empty())
      RegisterImportItem(pi, pi->name, typedefs, cu_param_scope);
  }
}

// Register a single named item of an explicitly-named package import.
static void RegisterNamedImport(const PackageDecl* pkg, std::string_view target,
                                TypedefMap& typedefs,
                                ScopeMap& cu_param_scope) {
  for (const auto* pi : pkg->items) {
    if (pi->name == target) {
      RegisterImportItem(pi, target, typedefs, cu_param_scope);
      break;
    }
  }
}

// Apply one package import directive, resolving the named package and
// registering either all of its items (wildcard) or a single named item.
static void ApplyImport(const ImportItem& import_item,
                        const CompilationUnit* unit, TypedefMap& typedefs,
                        ScopeMap& cu_param_scope) {
  const PackageDecl* pkg = FindPackageByName(unit, import_item.package_name);
  if (!pkg) return;
  if (import_item.is_wildcard) {
    RegisterWildcardImport(pkg, typedefs, cu_param_scope);
  } else {
    RegisterNamedImport(pkg, import_item.item_name, typedefs, cu_param_scope);
  }
}

// §26.4: an import written in the module header precedes every declaration in
// the module, ports included, so these are applied before ports and before the
// item walk. A body import is applied by ApplyBodyImport below instead, as the
// walk reaches it.
void Elaborator::ApplyHeaderImports(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    if (!item->import_item.is_header) continue;
    ApplyImport(item->import_item, unit_, typedefs_, cu_param_scope_);
  }
}

// §26.3: an identifier is potentially locally visible "at some point within a
// scope if there is a wildcard import of a package before that point within the
// current scope", and an explicit import makes one locally visible "prior to
// that point within the current scope". Both rules are about the import's
// position in the scope, which is why this registers one import as the item
// walk in Elaborator::ElaborateItems reaches it rather than hoisting every body
// import ahead of the walk: a declaration written above the import does not see
// the package, and one written below it does.
//
// A header import is already registered by ApplyHeaderImports before the walk
// starts and is skipped here.
void Elaborator::ApplyBodyImport(const ImportItem& import_item) {
  if (import_item.is_header) return;
  ApplyImport(import_item, unit_, typedefs_, cu_param_scope_);
}

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
  if (has_param_type && param_type != nullptr &&
      TryFoldRealParamValue(pd, pval, *param_type, scope))
    return;
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
                           val.pname),
               Subclause("6.20.7"));
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
                           pd.name, decl->name),
               Subclause("6.20.1"));
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
  mod->is_interface = (decl->decl_kind == ModuleDeclKind::kInterface);
  mod->delay_mode = unit->delay_mode_directive;
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

// What a parameter port declaration is built against, and the name table it is
// registered into. The three travel together because a parameter port cannot be
// built without the first two nor judged under §11.5.1 without the third, and
// etc/clang_tidy/src.yml caps a function at five parameters.
struct ParamPortCtx {
  const TypedefMap& typedefs;
  const ScopeMap& scope;
  std::unordered_set<std::string_view>& real_param_names;
};

// Build the non-value identity/type fields of a parameter declaration (name,
// localparam/type-param flags, declared-type info), and record a real-typed one
// in `ctx.real_param_names`. Value resolution is handled separately because it
// requires Elaborator member helpers.
//
// The registration is here rather than at the call site because §11.5.1 states
// "A bit-select or part-select of a scalar, or of a real variable or real
// parameter, shall be illegal", naming the parameter rather than the position
// the parameter was written in. PopulateValueParamInfo in
// src/elaborator/elaborator_items.cpp records a real parameter written in the
// module body into the same set, and CheckRealSelectNode in
// src/elaborator/elaborator_validate.cpp reads it for either position. A
// localparam port is recorded on the same terms, since §6.20.2 makes it a value
// parameter.
static RtlirParamDecl BuildParamDeclShell(const ModuleDecl* decl, size_t i,
                                          const ParamPortCtx& ctx,
                                          bool has_param_type) {
  const auto& [pname, pval] = decl->params[i];
  RtlirParamDecl pd;
  pd.name = pname;
  pd.default_value = pval;
  pd.is_resolved = false;
  pd.is_type_param = decl->type_param_names.count(pname) > 0;
  pd.is_localparam = decl->localparam_port_names.count(pname) > 0;
  if (has_param_type) {
    PopulateParamTypeInfo(pd, decl->param_types[i], ctx.typedefs, ctx.scope);
    RecordParamDeclRange(pd, decl->param_types[i], ctx.scope);
    if (IsRealType(decl->param_types[i].kind))
      ctx.real_param_names.insert(pname);
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

  // §26.3 and §6.18: a name an import or a typedef declaration introduces
  // belongs to the scope it was written in, so what this module adds to
  // typedefs_ and cu_param_scope_ is taken back out before the next module is
  // elaborated. Without this, `module a; import q::*; endmodule module b;
  // word_t y; endmodule` sizes b's y from a's import, and a typedef declared in
  // a is equally visible in b.
  //
  // These two are copied and put back rather than moved out and cleared like
  // the state above, because they also hold the compilation unit's own
  // declarations: RegisterCuScopeItems fills both with $unit's typedefs and
  // parameters and with every package parameter under its qualified key before
  // any module is elaborated, and §3.12.1 makes those visible to every module.
  // The snapshot keeps them and drops only what this module added.
  //
  // A module elaborated as a child instance still starts from its parent's
  // entry, which is what a lexically nested module (§23.4) requires and what a
  // separately instantiated one does not; that is a different question from the
  // one settled here, which is what one module leaves behind for the next.
  TypedefMap saved_typedefs = typedefs_;
  ScopeMap saved_cu_param_scope = cu_param_scope_;

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
    RtlirParamDecl pd = BuildParamDeclShell(
        decl, i, {typedefs_, scope, real_param_names_}, has_param_type);
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

  // §14.14 (rule b): a $global_clock reference resolves against the effective
  // global clocking found by searching up the instance hierarchy. Extend the
  // in-scope flag with this cell's own declaration before its items -- and the
  // child instances among them -- are elaborated, so a reference in a module
  // that does not itself declare a global clocking still resolves against an
  // ancestor's. Restored below so the flag reflects the parent's chain again.
  bool saved_global_clocking_in_scope = global_clocking_in_scope_;
  global_clocking_in_scope_ =
      saved_global_clocking_in_scope || ModuleDeclaresGlobalClocking(decl);

  ElaborateItems(decl, mod);
  ResolveExplicitPortTypes(decl, mod);
  global_clocking_in_scope_ = saved_global_clocking_in_scope;
  current_library_ = std::move(saved_library);
  enclosing_scope_names_ = std::move(saved_enclosing);
  typedefs_ = std::move(saved_typedefs);
  cu_param_scope_ = std::move(saved_cu_param_scope);
  saved_item_state.Restore(*this);
  return mod;
}

}  // namespace delta
