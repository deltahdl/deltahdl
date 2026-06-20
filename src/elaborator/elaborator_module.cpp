#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <format>
#include <optional>
#include <unordered_set>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
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

// Apply one header (package) import directive, resolving the named package and
// registering either all of its items (wildcard) or a single named item.
static void ApplyHeaderImport(const ImportItem& import_item,
                              const CompilationUnit* unit, TypedefMap& typedefs,
                              ScopeMap& cu_param_scope) {
  auto pkg_name = import_item.package_name;
  const PackageDecl* pkg = nullptr;
  for (const auto* p : unit->packages) {
    if (p->name == pkg_name) {
      pkg = p;
      break;
    }
  }
  if (!pkg) return;
  if (import_item.is_wildcard) {
    for (const auto* pi : pkg->items) {
      if (!pi->name.empty())
        RegisterHeaderImportItem(pi, pi->name, typedefs, cu_param_scope);
    }
  } else {
    auto target = import_item.item_name;
    for (const auto* pi : pkg->items) {
      if (pi->name == target) {
        RegisterHeaderImportItem(pi, target, typedefs, cu_param_scope);
        break;
      }
    }
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
static void ResolveUnresolvedParamValue(
    RtlirParamDecl& pd, const Expr* pval, std::string_view pname,
    const ScopeMap& scope, bool refers_to_unbounded, bool contains_dollar,
    bool has_param_type, const DataType* param_type, DiagEngine& diag) {
  if (pval->kind == ExprKind::kIdentifier && pval->text == "$") {
    pd.is_unbounded = true;
    return;
  }
  if (pval->kind == ExprKind::kIdentifier && refers_to_unbounded) {
    // §6.20.7: assigning a $ (unbounded) parameter to another parameter is
    // legal; the assigned-to parameter is itself unbounded.
    pd.is_unbounded = true;
    return;
  }
  if (contains_dollar) {
    // §6.20.7: $ must be the entire, self-contained parameter value; it
    // may not be combined with operators or selects in this context.
    diag.Error(pval->range.start,
               std::format("'$' may only be assigned to parameter '{}' "
                           "as a complete, self-contained expression",
                           pname));
  }
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

RtlirModule* Elaborator::ElaborateModule(const ModuleDecl* decl,
                                         const ParamList& params) {
  auto* mod = arena_.Create<RtlirModule>();
  mod->name = decl->name;

  mod->library = decl->library;

  // While this cell is elaborated it is the parent of any instances it
  // contains; record its library so child binding can fall back to it
  // (§33.4.1.5) or inherit it for a library-less use clause (§33.4.1.6). The
  // previous value is restored before returning.
  std::string saved_library = std::move(current_library_);
  current_library_.assign(decl->library.data(), decl->library.size());
  mod->has_param_port_list = decl->has_param_port_list;
  mod->is_program = (decl->decl_kind == ModuleDeclKind::kProgram);

  mod->delay_mode = unit_->delay_mode_directive;

  mod->attrs = ResolveAttributes(decl->attrs, diag_);

  RtlirImport std_import;
  std_import.package_name = "std";
  std_import.is_wildcard = true;
  mod->imports.push_back(std_import);

  ApplyHeaderImports(decl);

  for (size_t i = 0; i < decl->params.size(); ++i) {
    const auto& [pname, pval] = decl->params[i];
    RtlirParamDecl pd;
    pd.name = pname;
    pd.default_value = pval;
    pd.is_resolved = false;
    pd.is_type_param = decl->type_param_names.count(pname) > 0;
    pd.is_localparam = decl->localparam_port_names.count(pname) > 0;

    auto scope = BuildParamScope(mod);

    if (!pd.is_type_param && i < decl->param_types.size()) {
      PopulateParamTypeInfo(pd, decl->param_types[i], typedefs_, scope);
    }

    auto override_val = FindParamOverride(params, pname);
    if (override_val) {
      pd.resolved_value = ConvertOverrideValue(*override_val, pd);
      pd.is_resolved = true;
      pd.from_override = true;
    }
    if (!pd.is_resolved && pval) {
      bool has_param_type = !pd.is_type_param && i < decl->param_types.size();
      const DataType* param_type =
          has_param_type ? &decl->param_types[i] : nullptr;
      bool refers_to_unbounded = pval->kind == ExprKind::kIdentifier &&
                                 RefersToUnboundedParam(mod, pval->text);
      bool contains_dollar = ContainsDollarSubexpr(pval);
      ResolveUnresolvedParamValue(pd, pval, pname, scope, refers_to_unbounded,
                                  contains_dollar, has_param_type, param_type,
                                  diag_);
    }

    mod->params.push_back(pd);
  }

  ReportParamsMissingValue(decl, mod, diag_);

  ElaboratePorts(decl, mod);

  CheckConditionalGenerateNaming(decl);
  AssignGenerateBlockNames(decl);
  ElaborateItems(decl, mod);
  ResolveExplicitPortTypes(decl, mod);
  current_library_ = std::move(saved_library);
  return mod;
}

// Diagnose repeated port names: explicitly named (.name) ports in a non-ANSI
// header, and ordinary port names in an ANSI header (tracked across the run via
// ansi_port_names).
static void CheckDuplicatePortNames(
    const ModuleDecl* decl,
    std::unordered_set<std::string_view>& ansi_port_names, DiagEngine& diag) {
  if (decl->is_non_ansi_ports) {
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

  if (!decl->is_non_ansi_ports) {
    for (const auto& port : decl->ports) {
      if (!port.name.empty()) {
        if (!ansi_port_names.insert(port.name).second) {
          diag.Error(port.loc,
                     std::format("duplicate port name '{}'", port.name));
        }
      }
    }
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

void Elaborator::ElaboratePorts(const ModuleDecl* decl, RtlirModule* mod) {
  auto param_scope = BuildParamScope(mod);

  CheckDuplicatePortNames(decl, ansi_port_names_, diag_);

  for (const auto& port : decl->ports) {
    if (port.data_type.kind == DataTypeKind::kChandle) {
      diag_.Error(port.loc, "chandle cannot be used as a port type");
      continue;
    }
    if (port.data_type.kind == DataTypeKind::kVirtualInterface) {
      diag_.Error(port.loc, "virtual interface cannot be used as a port type");
      continue;
    }

    if (decl->is_non_ansi_ports && !port.name.empty() &&
        !port.is_explicit_named && port.direction == Direction::kNone) {
      diag_.Error(port.loc,
                  std::format("port '{}' has no direction declaration in the "
                              "module body",
                              port.name));
    }

    if (decl->is_non_ansi_ports && !port.name.empty() &&
        port.direction != Direction::kNone) {
      if (port.data_type.kind != DataTypeKind::kImplicit) {
        non_ansi_complete_ports_.insert(port.name);
      } else {
        non_ansi_partial_ports_[port.name] =
            EvalTypeWidth(port.data_type, typedefs_, param_scope);
        // §23.2.2.1: remember a `signed` port direction declaration so the
        // matching net/variable declaration can be considered signed too.
        if (port.data_type.is_signed) non_ansi_signed_ports_.insert(port.name);
      }
    }

    if (port.default_value) {
      ValidatePortDefaultValue(port, decl->is_non_ansi_ports, diag_);
    }

    // §23.2.2.1: it is illegal to specify `signed` for a port declared as an
    // interconnect port. Interconnect is an untyped generic connection, so it
    // carries no signedness of its own.
    if (port.data_type.is_interconnect && port.data_type.is_signed) {
      diag_.Error(port.loc,
                  std::format("interconnect port '{}' shall not be declared "
                              "signed",
                              port.name));
    }

    bool port_is_var =
        !port.data_type.is_net && !port.data_type.is_interconnect;

    if (port.direction == Direction::kInout && port_is_var) {
      diag_.Error(port.loc,
                  std::format("variable data type is not permitted on "
                              "inout port '{}'",
                              port.name));
    }

    RtlirPort rp;
    rp.name = port.name;
    rp.direction = port.direction;
    rp.type_kind = port.data_type.kind;
    rp.width = EvalTypeWidth(port.data_type, typedefs_, param_scope);
    rp.is_signed = port.data_type.is_signed;
    rp.is_var = port_is_var;
    rp.is_interconnect = port.data_type.is_interconnect;
    rp.default_value = port.default_value;

    ComputePortUnpackedDimSizes(port, rp);

    if (port.is_interface_port) {
      rp.is_interface_port = true;
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
