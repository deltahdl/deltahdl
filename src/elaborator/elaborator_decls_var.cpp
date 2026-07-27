#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <format>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_decls_internal.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

static void ValidateParameterizedClassDefaults(const ModuleItem* item,
                                               const CompilationUnit* unit,
                                               DiagEngine& diag) {
  if (!item->data_type.type_params.empty()) return;
  const auto* cls = FindClassDecl(item->data_type.type_name, unit);
  if (!cls || cls->params.empty()) return;
  for (const auto& [pname, pexpr] : cls->params) {
    if (!pexpr && !cls->type_param_names.count(pname)) {
      diag.Error(item->loc,
                 std::format("parameterized class '{}' has no default "
                             "specialization; parameter '{}' has no "
                             "default value",
                             cls->name, pname));
      break;
    }
  }
}

static void ValidateWeakReferenceTypeParam(
    const ModuleItem* item, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names, DiagEngine& diag) {
  if (item->data_type.type_name != "weak_reference" ||
      item->data_type.type_params.empty()) {
    return;
  }
  const auto& tp = item->data_type.type_params[0];
  if (!WeakRefTypeParamNamesClass(tp, typedefs, class_names)) {
    diag.Error(item->loc,
               "weak_reference type parameter shall be a class type");
  }
}

void Elaborator::ValidateVarDeclTypes(ModuleItem* item, const ScopeMap& scope) {
  if (item->data_type.kind == DataTypeKind::kNamed &&
      class_names_.count(item->data_type.type_name)) {
    class_var_names_.insert(item->name);
    class_var_types_[item->name] = item->data_type.type_name;
    ValidateParameterizedClassDefaults(item, unit_, diag_);
    ValidateWeakReferenceTypeParam(item, typedefs_, class_names_, diag_);
  }
  if (item->data_type.kind == DataTypeKind::kEnum) {
    ValidateEnumDecl(item->data_type, item->loc);
  }
  if (item->data_type.kind == DataTypeKind::kStruct ||
      item->data_type.kind == DataTypeKind::kUnion) {
    ValidatePackedStructDefaults(item->data_type, item->loc);
    ValidateUnpackedStructWithUnionDefaults(item->data_type, item->loc);
    ValidateStructMemberDefaultsConstant(item->data_type, item->loc, scope);
    ValidateVoidMembers(item->data_type, item->loc);
    ValidateRandQualifiers(item->data_type, item->loc);
    ValidatePackedDimRequiresPackedKeyword(item->data_type, item->loc);
    ValidatePackedStructMemberTypes(item->data_type, item->loc);
    ValidateChandleInUnion(item->data_type, item->loc);
    ValidateVirtualInterfaceInUnion(item->data_type, item->loc);
    ValidatePackedUnion(item->data_type, item->loc);
  }
  ValidatePackedDimOnPredefinedType(item->data_type, item->loc);
  ValidatePackedDimOnDisallowedType(item->data_type, item->loc);
  ValidateAssocIndexType(item);
}

static void CollectUnpackedDimSizes(const std::vector<Expr*>& dims,
                                    std::vector<uint32_t>& dim_los,
                                    std::vector<uint32_t>& dim_sizes,
                                    const ScopeMap& scope) {
  for (auto* dim : dims) {
    if (!dim) continue;
    if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
      // §7.4.2 / §11.2.1: bounds may name parameters, so evaluate every
      // dimension in the module's parameter scope (mirrors
      // ComputeUnpackedDims).
      auto lv = ConstEvalInt(dim->lhs, scope);
      auto rv = ConstEvalInt(dim->rhs, scope);
      if (!lv || !rv) continue;
      dim_los.push_back(static_cast<uint32_t>(std::min(*lv, *rv)));
      dim_sizes.push_back(static_cast<uint32_t>(std::abs(*lv - *rv) + 1));
    } else if (auto sv = ConstEvalInt(dim, scope); sv && *sv > 0) {
      dim_los.push_back(0);
      dim_sizes.push_back(static_cast<uint32_t>(*sv));
    }
  }
}

void Elaborator::TrackVarArrayInfo(const ModuleItem* item, RtlirVariable& var,
                                   const ScopeMap& scope) {
  if (item->unpacked_dims.empty()) return;
  VarArrayInfo info{item->data_type.kind,
                    var.unpacked_size,
                    static_cast<uint32_t>(item->unpacked_dims.size()),
                    var.width,
                    var.is_signed,
                    var.is_4state,
                    var.is_dynamic,
                    var.is_assoc,
                    {},
                    {}};
  info.is_queue = var.is_queue;
  if (var.is_assoc && item->unpacked_dims[0] &&
      item->unpacked_dims[0]->kind == ExprKind::kIdentifier) {
    info.assoc_index_type = item->unpacked_dims[0]->text;
  }
  std::vector<uint32_t> dim_los;
  CollectUnpackedDimSizes(item->unpacked_dims, dim_los, info.dim_sizes, scope);
  var_array_info_[item->name] = info;
  // §7.4.2: carry full per-dimension extents to the simulator only when every
  // dimension is a fixed const size — queue/dynamic/assoc dims fall short of
  // the declared count, so the single-dimension unpacked_size/lo stays in
  // force.
  if (info.dim_sizes.size() >= 2 &&
      info.dim_sizes.size() == item->unpacked_dims.size()) {
    var.unpacked_dim_los = std::move(dim_los);
    var.unpacked_dim_sizes = info.dim_sizes;
  }
}

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
  return false;
}

// §25.9: record explicit parameter overrides of a virtual interface variable
// when they all evaluate to constants, so a later assignment can confirm the
// actual parameter values match the interface it is assigned from.
void RecordViParamOverrides(
    const ModuleItem* item,
    std::unordered_map<std::string_view, std::vector<int64_t>>& param_values,
    const ScopeMap& scope) {
  if (item->data_type.type_params.empty()) return;
  std::vector<int64_t> values;
  bool all_const = true;
  for (const auto& tp : item->data_type.type_params) {
    if (tp.type_ref_expr == nullptr) {
      all_const = false;
      break;
    }
    // §25.9 / §11.2.1: an override may be any constant expression, including a
    // parameter or localparam of the enclosing scope, so evaluate it in the
    // module's parameter scope rather than an empty one.
    auto v = ConstEvalInt(tp.type_ref_expr, scope);
    if (!v) {
      all_const = false;
      break;
    }
    values.push_back(*v);
  }
  if (all_const) {
    param_values[item->name] = std::move(values);
  }
}

// §6.8 / §6.11: classify a scalar variable's element kind flags from its data
// type. Width/signedness/struct/enum info is filled in separately.
void SetVariableKindFlags(const ModuleItem* item, RtlirVariable& var,
                          const TypedefMap& typedefs) {
  var.is_4state = Is4stateType(item->data_type, typedefs);
  var.is_event = (item->data_type.kind == DataTypeKind::kEvent);
  var.is_chandle = (item->data_type.kind == DataTypeKind::kChandle);
  var.is_string = (item->data_type.kind == DataTypeKind::kString);
  var.is_real = (item->data_type.kind == DataTypeKind::kReal ||
                 item->data_type.kind == DataTypeKind::kShortreal ||
                 item->data_type.kind == DataTypeKind::kRealtime);
}

// §6.6.7: tag a net produced from a user-defined nettype with its nettype name
// and resolution function (if any).
void TagUserNettypeNet(
    const ModuleItem* item, RtlirNet& net,
    const std::unordered_map<std::string_view, std::string_view>&
        resolve_funcs) {
  net.is_user_nettype = true;
  net.nettype_name = item->data_type.type_name;
  auto it = resolve_funcs.find(item->data_type.type_name);
  if (it != resolve_funcs.end()) {
    net.resolve_func = it->second;
  }
}

// §25.9: validate that a virtual interface declaration names a real interface,
// a modport that exists on it, and an interface free of external references.
void ValidateVirtualInterfaceTarget(const ModuleItem* item,
                                    const ModuleDecl* iface_decl,
                                    std::string_view iface_name,
                                    std::string_view modport_name,
                                    DiagEngine& diag) {
  if (!iface_decl || iface_decl->decl_kind != ModuleDeclKind::kInterface) {
    diag.Error(item->loc,
               std::format("unknown interface '{}' in virtual interface "
                           "declaration",
                           iface_name));
  } else if (!modport_name.empty()) {
    bool found = false;
    for (const auto* mp : iface_decl->modports) {
      if (mp && mp->name == modport_name) {
        found = true;
        break;
      }
    }
    if (!found) {
      diag.Error(item->loc,
                 std::format("modport '{}' not found in interface '{}'",
                             modport_name, iface_name));
    }
  }
  // §25.9: an interface containing hierarchical references to objects outside
  // its body (or ports that reference other interfaces) shall not be used as
  // the type of a virtual interface.
  if (iface_decl && iface_decl->decl_kind == ModuleDeclKind::kInterface &&
      InterfaceContainsExternalReference(iface_decl)) {
    diag.Error(item->loc,
               std::format("interface '{}' contains references to objects "
                           "outside its body and cannot be used as a "
                           "virtual interface",
                           iface_name));
  }
}

}  // namespace

// §6.11 / §6.20 / §23.2.2.1: bundle of name-table state updated while
// registering a variable declaration's name (const-ness, kind, shape, named
// type).
struct VarDeclNameTables {
  std::unordered_set<std::string_view>& const_names;
  std::unordered_set<std::string_view>& const_var_names;
  std::unordered_map<std::string_view, DataTypeKind>& var_types;
  std::unordered_set<std::string_view>& scalar_var_names;
  std::unordered_set<std::string_view>& packed_array_vars;
  std::unordered_map<std::string_view, std::string_view>& var_named_types;
};

// §6.11.1 / Table 6-8: the integer atom types (byte, shortint, int, longint,
// integer, time) are multi-bit vector types with a fixed implicit width, not
// scalars. Per §11.5.1 a bit-select or part-select of a scalar is illegal, but
// these vector types are freely bit/part-selectable, so they must not be
// classified as scalars even though they carry no explicit packed dimension.
static bool IsIntegerAtomKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kInteger:
    case DataTypeKind::kLongint:
    case DataTypeKind::kTime:
      return true;
    default:
      return false;
  }
}

// §11.5.1 / §7.4.1: a packed structure or packed union presents as a single
// contiguous vector, and §11.5.1 lists a packed structure among the operands a
// bit-select or part-select may address. A variable of packed aggregate type is
// therefore freely bit/part-selectable and must not be treated as a scalar,
// even though it carries no explicit packed dimension of its own. Named types
// are followed through the typedef map to the underlying aggregate.
static bool IsPackedAggregateVar(const DataType& dtype,
                                 const TypedefMap& typedefs) {
  const DataType* d = &dtype;
  for (int hops = 0; hops < 16 && d->kind == DataTypeKind::kNamed; ++hops) {
    auto it = typedefs.find(d->type_name);
    if (it == typedefs.end()) return false;
    d = &it->second;
  }
  return (d->kind == DataTypeKind::kStruct ||
          d->kind == DataTypeKind::kUnion) &&
         (d->is_packed || d->is_soft);
}

// §6.11 / §6.20: record the bookkeeping name tables for a variable declaration
// (const-ness, type kind, scalar/packed-array shape, named type) before the
// RtlirVariable is built.
static void RegisterVarDeclNames(const ModuleItem* item,
                                 VarDeclNameTables tables,
                                 const TypedefMap& typedefs, DiagEngine& diag) {
  if (item->data_type.is_const) {
    // §17.7: a constant free checker variable (rand const) need not be
    // initialized; an uninitialized one simply takes a nondeterministic
    // constant value that never changes. The general requirement that a const
    // variable be initialized therefore does not apply to a free variable.
    if (!item->init_expr && !item->is_rand) {
      diag.Error(
          item->loc,
          std::format("const variable '{}' must be initialized", item->name));
    }
    tables.const_names.insert(item->name);
    tables.const_var_names.insert(item->name);
  }
  tables.var_types[item->name] = item->data_type.kind;
  // §7.4/§7.8: a variable carrying an unpacked dimension (fixed, dynamic,
  // queue, or associative array) is neither a scalar nor a packed-array
  // variable for select-legality purposes; indexing it is a legal array
  // select, not a bit-select of a scalar. Only dimensionless variables are
  // classified here.
  if (item->unpacked_dims.empty()) {
    if (item->data_type.packed_dim_left)
      tables.packed_array_vars.insert(item->name);
    else if (!IsIntegerAtomKind(item->data_type.kind) &&
             !IsPackedAggregateVar(item->data_type, typedefs))
      tables.scalar_var_names.insert(item->name);
  }
  if (item->data_type.kind == DataTypeKind::kNamed)
    tables.var_named_types[item->name] = item->data_type.type_name;
}

// §25.9: bundle of virtual-interface name-table state updated while registering
// a virtual interface variable declaration.
struct VirtualInterfaceVarTables {
  std::unordered_map<std::string_view, std::string_view>&
      vi_var_interface_types;
  std::unordered_map<std::string_view, std::string_view>& vi_var_modports;
  std::unordered_map<std::string_view, std::vector<int64_t>>&
      vi_var_param_values;
};

// §25.9: register a virtual interface variable's interface/modport bindings and
// validate the named interface target (`iface_decl` is the resolved interface,
// or null when unknown).
static void RegisterVirtualInterfaceVarDecl(const ModuleItem* item,
                                            const ModuleDecl* iface_decl,
                                            VirtualInterfaceVarTables tables,
                                            const ScopeMap& scope,
                                            DiagEngine& diag) {
  if (item->data_type.kind != DataTypeKind::kVirtualInterface) return;
  auto iface_name = item->data_type.type_name;
  auto modport_name = item->data_type.modport_name;
  tables.vi_var_interface_types[item->name] = iface_name;
  tables.vi_var_modports[item->name] = modport_name;
  RecordViParamOverrides(item, tables.vi_var_param_values, scope);
  ValidateVirtualInterfaceTarget(item, iface_decl, iface_name, modport_name,
                                 diag);
}

// §6.18 / §7.4 / §10.10.1: when a variable's named type is a fixed unpacked-
// array typedef and it declares no unpacked dimensions of its own, rewrite it
// to the typedef's element base type (keeping its own const-ness) plus the
// typedef's unpacked dimensions, so it elaborates and lowers identically to an
// inline unpacked-array declaration. Returns the adopted typedef name (empty
// when no rewrite happened) so the caller can keep the variable's named-type
// association, which the rewrite to a non-named base type would otherwise drop.
static std::string_view AdoptTypedefArrayDims(
    ModuleItem* item, const TypedefMap& typedefs,
    const std::unordered_map<std::string_view, std::vector<Expr*>>&
        td_array_dims) {
  if (!item->unpacked_dims.empty()) return {};
  if (item->data_type.kind != DataTypeKind::kNamed) return {};
  auto dims_it = td_array_dims.find(item->data_type.type_name);
  if (dims_it == td_array_dims.end()) return {};
  auto base_it = typedefs.find(item->data_type.type_name);
  if (base_it == typedefs.end()) return {};
  std::string_view typedef_name = item->data_type.type_name;
  bool was_const = item->data_type.is_const;
  item->data_type = base_it->second;
  item->data_type.is_const = was_const;
  item->unpacked_dims = dims_it->second;
  return typedef_name;
}

void Elaborator::ElaborateVarDecl(ModuleItem* item, RtlirModule* mod) {
  ResolveTypeRef(item, mod);

  ResolveParameterizedType(item->data_type);

  std::string_view adopted_array_typedef =
      AdoptTypedefArrayDims(item, typedefs_, td_array_dims_);

  if (item->data_type.kind == DataTypeKind::kNamed &&
      nettype_names_.count(item->data_type.type_name)) {
    item->data_type.is_net = true;
    item->kind = ModuleItemKind::kNetDecl;
    nettype_net_names_.insert(item->name);
    ElaborateNetDecl(item, mod);
    TagUserNettypeNet(item, mod->nets.back(), nettype_resolve_funcs_);
    return;
  }

  if (item->is_automatic) {
    diag_.Error(item->loc,
                "automatic lifetime is not allowed on module-level variables");
  }
  CheckDeclRedeclaration(
      item, {item->data_type, typedefs_},
      {ansi_port_names_, non_ansi_complete_ports_, non_ansi_partial_ports_,
       declared_names_, ScopedName(item->name)},
      "variable", diag_);

  RegisterVarDeclNames(
      item,
      {const_names_, const_var_names_, var_types_, scalar_var_names_,
       packed_array_vars_, var_named_types_},
      typedefs_, diag_);
  // §10.10.1 / §11.2.2: keep the named-type association for a variable that
  // adopted a typedef array's dimensions above; rewriting it to a non-named
  // base type kept RegisterVarDeclNames from recording it, but aggregate
  // type-equivalence checks still need to know its declared array typedef.
  if (!adopted_array_typedef.empty()) {
    var_named_types_[item->name] = adopted_array_typedef;
  }
  const ModuleDecl* vi_iface_decl =
      item->data_type.kind == DataTypeKind::kVirtualInterface
          ? FindModule(item->data_type.type_name)
          : nullptr;
  RegisterVirtualInterfaceVarDecl(
      item, vi_iface_decl,
      {vi_var_interface_types_, vi_var_modports_, vi_var_param_values_},
      BuildParamScope(mod), diag_);

  RtlirVariable var;
  var.name = ScopedName(item->name);
  // A packed dimension may reference a parameter (e.g. `logic [W-1:0]`), so the
  // width must be evaluated in the module's parameter scope (10.3.3 / A.2.2.1).
  var.width = EvalTypeWidth(item->data_type, typedefs_, BuildParamScope(mod));
  ValidatePackedDimRange(item->data_type, item->loc);
  SetVariableKindFlags(item, var, typedefs_);
  var.is_signed = IsSignedType(item->data_type, typedefs_);
  if (non_ansi_partial_ports_.count(item->name)) {
    var.is_signed =
        ReconcilePartialPortSignedness(item->name, var.is_signed, mod);
  }
  var.elem_type_kind = item->data_type.kind;
  var.init_expr = item->init_expr;

  if (item->init_expr) {
    var_init_names_.insert(item->name);
  }

  SetVariableTypeInfo(item, var);

  ComputeUnpackedDims(
      item->unpacked_dims, var,
      {{typedefs_, class_names_}, BuildParamScope(mod), diag_, item->loc});
  ValidateUnpackedDimRange(item->unpacked_dims, item->loc);
  InferDynArraySize(item->unpacked_dims, item->init_expr, var);

  TrackVarArrayInfo(item, var, BuildParamScope(mod));

  var.attrs = ResolveAttributes(item->attrs, diag_, BuildParamScope(mod));
  mod->variables.push_back(var);
  ValidateArrayInitPattern(item);
  ValidateStructInitPattern(item);

  ValidateVarDeclTypes(item, BuildParamScope(mod));
  TrackEnumVariable(item);
}

}  // namespace delta
