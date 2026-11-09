#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/aggregate_shape.h"
#include "elaborator/assoc_index_type.h"
#include "elaborator/class_base_resolution.h"
#include "elaborator/class_default_specialization.h"
#include "elaborator/const_eval.h"
#include "elaborator/covergroup_variables.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_array_shape.h"
#include "elaborator/elaborator_class_typedef_specialization.h"
#include "elaborator/elaborator_data.h"
#include "elaborator/elaborator_decls_internal.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/net_data_type.h"
#include "elaborator/nettype_uses.h"
#include "elaborator/param_value_assignability.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_param_scope_prefix.h"
#include "elaborator/virtual_interface_target.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

static bool IsIntegralKeywordKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kBit:
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
      return true;
    default:
      return false;
  }
}

void SetPackedTypedefTypeInfo(const ModuleItem* item, RtlirVariable& var,
                              const TypedefMap& typedefs, Arena& arena) {
  if (var.dtype != nullptr || item->data_type.kind != DataTypeKind::kNamed ||
      item->data_type.packed_dim_left != nullptr) {
    return;
  }
  const DataType* bound = FindNamedType(item->data_type, typedefs);
  if (bound == nullptr || bound->kind == DataTypeKind::kNamed ||
      (bound->packed_dim_left == nullptr &&
       !IsIntegralKeywordKind(bound->kind))) {
    return;
  }
  var.dtype = arena.Create<DataType>(*bound);
}

static void ValidateParameterizedClassDefaults(const ModuleItem* item,
                                               const CompilationUnit* unit,
                                               DiagEngine& diag) {
  if (!item->data_type.type_params.empty()) return;
  const auto* cls = FindClassDecl(item->data_type.type_name, unit);
  if (cls == nullptr) return;
  const std::string_view kMissing = ParameterWithoutDefault(*cls);
  if (kMissing.empty()) return;
  diag.Error(item->loc,
             std::format("parameterized class '{}' has no default "
                         "specialization; parameter '{}' has no default value",
                         cls->name, kMissing),
             Subclause("8.25"));
}

static void ValidateSpecializationArgsConstant(const ModuleItem* item,
                                               const ScopeMap& scope,
                                               DiagEngine& diag) {
  for (const auto& tp : item->data_type.type_params) {
    if (!tp.type_name.empty() || tp.type_ref_expr == nullptr) continue;
    if (IsConstantClassParamValue(tp.type_ref_expr, scope)) continue;
    diag.Error(tp.type_ref_expr->range.start,
               std::format("class '{}' parameter override is not a constant "
                           "expression",
                           item->data_type.type_name),
               Subclause("23.10.2"));
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
               "weak_reference needs a class type as its type parameter",
               Subclause("8.30.1"));
  }
}

static void ResolveDeclaredTypeName(
    ModuleItem* item, const CompilationUnit* unit, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names, DiagEngine& diag) {
  DataType& dtype = item->data_type;
  ResolveParameterizedType(dtype, unit, diag, item->loc);
  if (dtype.kind != DataTypeKind::kNamed) return;
  if (class_names.count(dtype.type_name) > 0) return;
  const DataType* bound = FindNamedType(dtype, typedefs);
  for (size_t depth = 0; depth < typedefs.size() && bound != nullptr &&
                         bound->kind == DataTypeKind::kNamed;
       ++depth) {
    if (class_names.count(bound->type_name) > 0) {
      dtype.type_name = bound->type_name;
      dtype.scope_name = bound->scope_name;
      dtype.type_params = bound->type_params;
      return;
    }
    bound = FindNamedType(*bound, typedefs);
  }
}

void Elaborator::ValidateVarDeclTypes(ModuleItem* item, const ScopeMap& scope,
                                      bool writes_its_type) {
  if (item->data_type.kind == DataTypeKind::kNamed &&
      class_names_.count(item->data_type.type_name)) {
    if (item->unpacked_dims.empty()) class_var_names_.insert(item->name);
    class_var_types_[item->name] = item->data_type.type_name;
    ValidateParameterizedClassDefaults(item, unit_, diag_);
    ReportSpecializationOverrideMismatches(item->data_type, item->loc, unit_,
                                           typedefs_, diag_);
    ReportSpecializationBaseNotClass(item->data_type, item->loc, *unit_, diag_);
    ValidateSpecializationArgsConstant(item, scope, diag_);
    ValidateWeakReferenceTypeParam(item, typedefs_, class_names_, diag_);
  }
  if (item->data_type.kind == DataTypeKind::kEnum && writes_its_type) {
    ValidateEnumDecl(item->data_type, item->loc, item->first_in_decl_list);
  }
  const TypeShapeTables kShapeTables{typedefs_, td_array_dims_, class_names_};
  CheckAggregateShape(item->data_type, item->loc,
                      {kShapeTables, &scope, diag_});
  ValidatePackedDimOnPredefinedType(item->data_type, item->loc);
  ValidatePackedDimOnDisallowedType(item->data_type, item->loc);
  CheckRealAssocIndexTypes(item->unpacked_dims, item->loc, typedefs_, diag_);
}

static void CollectUnpackedDimSizes(
    const std::vector<Expr*>& dims,
    std::vector<ElaboratorData::DeclaredDim>& declared_dims,
    std::vector<uint32_t>& dim_sizes, const ScopeMap& scope) {
  for (auto* dim : dims) {
    if (!dim) continue;
    if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
      auto lv = ConstEvalInt(dim->lhs, scope);
      auto rv = ConstEvalInt(dim->rhs, scope);
      if (!lv || !rv) continue;
      declared_dims.push_back({*lv, *rv});
      dim_sizes.push_back(static_cast<uint32_t>(std::abs(*lv - *rv) + 1));
    } else if (auto sv = ConstEvalInt(dim, scope); sv && *sv > 0) {
      declared_dims.push_back({0, *sv - 1});
      dim_sizes.push_back(static_cast<uint32_t>(*sv));
    }
  }
}

void Elaborator::TrackVarArrayInfo(
    const ModuleItem* item, RtlirVariable& var, const ScopeMap& scope,
    std::unordered_map<std::string_view, VarArrayInfo>& out) {
  if (item->unpacked_dims.empty()) return;
  VarArrayInfo info{ElementKindThroughTypedefs(item->data_type, typedefs_),
                    var.unpacked_size,
                    static_cast<uint32_t>(item->unpacked_dims.size()),
                    var.width,
                    var.is_signed,
                    var.is_4state,
                    var.is_dynamic,
                    var.is_assoc,
                    {},
                    {},
                    {}};
  info.is_queue = var.is_queue;
  info.elements_are_queues = var.elements_are_queues;
  info.elem_type_name = ElementTypeIdentity(item->data_type, typedefs_);
  info.elem_data_type = &item->data_type;
  std::vector<std::string_view> names;
  info.elem_is_unpacked_aggregate =
      IsUnpackedAggregate(FollowTypedefs(item->data_type, typedefs_, names));
  if (var.is_assoc && item->unpacked_dims[0] &&
      item->unpacked_dims[0]->kind == ExprKind::kIdentifier) {
    info.assoc_index_type = item->unpacked_dims[0]->text;
  }
  CollectUnpackedDimSizes(item->unpacked_dims, info.declared_dims,
                          info.dim_sizes, scope);
  info.unpacked_shape = UnpackedShapeOf(item->data_type, item->unpacked_dims,
                                        aggregate_typedef_names_, scope);
  out[item->name] = info;
  var.num_unpacked_dims = static_cast<uint32_t>(item->unpacked_dims.size());
  var.declared_unpacked_dims = &item->unpacked_dims;
  var.unpacked_dims.reserve(info.declared_dims.size());
  for (const auto& dim : info.declared_dims) {
    var.unpacked_dims.push_back({dim.left, dim.right});
  }
  if (info.dim_sizes.size() == item->unpacked_dims.size()) {
    var.unpacked_dim_sizes = info.dim_sizes;
  }
}

namespace {

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

void SetVariableKindFlags(const ModuleItem* item, RtlirVariable& var,
                          const TypedefMap& typedefs) {
  var.decl_kind = item->data_type.kind;
  var.is_4state = Is4stateType(item->data_type, typedefs);
  var.is_event = (item->data_type.kind == DataTypeKind::kEvent);
  var.is_chandle = (item->data_type.kind == DataTypeKind::kChandle);
  var.is_string = IsStringType(item->data_type, typedefs);
  var.is_real = (item->data_type.kind == DataTypeKind::kReal ||
                 item->data_type.kind == DataTypeKind::kShortreal ||
                 item->data_type.kind == DataTypeKind::kRealtime);
}

void TagUserNettypeNet(
    std::string_view nettype, RtlirNet& net,
    const std::unordered_map<std::string_view, std::string_view>&
        resolve_funcs) {
  net.is_user_nettype = true;
  net.nettype_name = nettype;
  auto it = resolve_funcs.find(nettype);
  if (it != resolve_funcs.end()) {
    net.resolve_func = it->second;
  }
}

}  // namespace

struct VarDeclNameTables {
  std::unordered_set<std::string_view>& const_names;
  std::unordered_set<std::string_view>& const_var_names;
  std::unordered_map<std::string_view, DataTypeKind>& var_types;
  std::unordered_set<std::string_view>& scalar_var_names;
  std::unordered_set<std::string_view>& real_var_names;
  std::unordered_set<std::string_view>& packed_array_vars;
  std::unordered_map<std::string_view, std::string_view>& var_named_types;
  std::unordered_map<std::string_view, VarSelectShape>& var_select_shapes;
};

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

static bool NamesVectorType(const DataType& dtype, const TypedefMap& typedefs) {
  if (dtype.kind != DataTypeKind::kNamed) return false;
  const DataType* d = TypeAtChainEnd(dtype, typedefs);
  if (d == nullptr) return false;
  return d->packed_dim_left != nullptr || !d->extra_packed_dims.empty() ||
         d->has_unsized_packed_dim || !d->enum_array_dims.empty() ||
         IsIntegerAtomKind(d->kind);
}

static bool IsPackedAggregateVar(const DataType& dtype,
                                 const TypedefMap& typedefs) {
  const DataType* d = TypeAtChainEnd(dtype, typedefs);
  if (!d) return false;
  return (d->kind == DataTypeKind::kStruct ||
          d->kind == DataTypeKind::kUnion) &&
         (d->is_packed || d->is_soft);
}

static bool IsStringVar(const DataType& dtype, const TypedefMap& typedefs) {
  const DataType* d = TypeAtChainEnd(dtype, typedefs);
  return d != nullptr && d->kind == DataTypeKind::kString;
}

bool DeclaresScalar(const DataType& dtype, const TypedefMap& typedefs) {
  return !IsIntegerAtomKind(dtype.kind) && !IsRealType(dtype.kind) &&
         dtype.enum_array_dims.empty() &&
         !IsPackedAggregateVar(dtype, typedefs) &&
         !NamesVectorType(dtype, typedefs) && !IsStringVar(dtype, typedefs);
}

void RecordVarSelectShape(
    const ModuleItem* item, const TypedefMap& typedefs,
    std::unordered_map<std::string_view, VarSelectShape>& shapes) {
  const DataType& dtype = item->data_type;
  const bool kIsAtom = IsIntegerAtomKind(dtype.kind);
  const bool kIsPackedAggregate = IsPackedAggregateVar(dtype, typedefs);
  const bool kIsScalarKind =
      dtype.kind == DataTypeKind::kLogic || dtype.kind == DataTypeKind::kReg ||
      dtype.kind == DataTypeKind::kBit || IsNetTypeKind(dtype.kind);
  if (!IsRealType(dtype.kind) && !kIsAtom && !kIsPackedAggregate &&
      !kIsScalarKind) {
    return;
  }
  size_t vector_dims = (dtype.packed_dim_left ? 1 : 0) +
                       dtype.extra_packed_dims.size() +
                       (dtype.has_unsized_packed_dim ? 1 : 0);
  if (kIsAtom || kIsPackedAggregate) ++vector_dims;
  VarSelectShape shape;
  shape.addressable_dims = item->unpacked_dims.size() + vector_dims;
  shape.element_is_real = IsRealType(dtype.kind);
  shape.element_is_scalar = !shape.element_is_real;
  shapes[item->name] = shape;
}

static void RegisterVarDeclNames(const ModuleItem* item,
                                 VarDeclNameTables tables,
                                 const TypedefMap& typedefs, DiagEngine& diag) {
  if (item->data_type.is_const) {
    if (!item->init_expr && !item->is_rand) {
      diag.Error(
          item->loc,
          std::format("const variable '{}' must be initialized", item->name),
          Subclause("6.20.6"));
    }
    tables.const_names.insert(item->name);
    tables.const_var_names.insert(item->name);
  }
  tables.var_types[item->name] = item->data_type.kind;
  if (item->unpacked_dims.empty()) {
    if (IsRealType(item->data_type.kind))
      tables.real_var_names.insert(item->name);
    if (item->data_type.packed_dim_left)
      tables.packed_array_vars.insert(item->name);
    else if (DeclaresScalar(item->data_type, typedefs))
      tables.scalar_var_names.insert(item->name);
  }
  if (item->data_type.kind == DataTypeKind::kNamed)
    tables.var_named_types[item->name] = item->data_type.type_name;
  RecordVarSelectShape(item, typedefs, tables.var_select_shapes);
}

struct VirtualInterfaceVarTables {
  std::unordered_map<std::string_view, std::string_view>&
      vi_var_interface_types;
  std::unordered_map<std::string_view, std::string_view>& vi_var_modports;
  std::unordered_map<std::string_view, std::vector<int64_t>>&
      vi_var_param_values;
};

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
  ValidateVirtualInterfaceTarget(item->data_type, item->loc, iface_decl, diag);
}

static std::string_view AdoptTypedefArrayDims(
    ModuleItem* item, const TypedefMap& typedefs,
    const std::unordered_map<std::string_view, std::vector<Expr*>>&
        td_array_dims) {
  if (!item->unpacked_dims.empty()) return {};
  if (item->data_type.kind != DataTypeKind::kNamed) return {};
  if (!item->data_type.scope_name.empty()) return {};
  auto base_it = typedefs.find(item->data_type.type_name);
  if (base_it == typedefs.end()) return {};
  auto dims_it = td_array_dims.find(item->data_type.type_name);
  if (dims_it == td_array_dims.end()) return {};
  std::string_view typedef_name = item->data_type.type_name;
  bool was_const = item->data_type.is_const;
  item->data_type = base_it->second;
  item->data_type.is_const = was_const;
  item->unpacked_dims = dims_it->second;
  return typedef_name;
}

bool Elaborator::ElaborateUserNettypeNet(ModuleItem* item, RtlirModule* mod) {
  if (item->data_type.kind != DataTypeKind::kNamed) return false;
  auto it = nettype_names_.find(NamedTypeKey(item->data_type));
  if (it == nettype_names_.end()) return false;
  std::string_view nettype = *it;
  if (WrittenAsDataDeclaration(item)) {
    ReportNettypeNotNet(nettype, std::format("variable '{}'", item->name),
                        item->loc, diag_);
    return false;
  }
  if (item->net_delay_fall != nullptr) {
    diag_.Error(item->loc,
                "a net of a user-defined nettype is declared with at most a "
                "single delay",
                Subclause("10.3.3"));
  }
  item->data_type.is_net = true;
  item->kind = ModuleItemKind::kNetDecl;
  nettype_net_names_.insert(item->name);
  ElaborateNetDecl(item, mod);
  TagUserNettypeNet(nettype, mod->nets.back(), nettype_resolve_funcs_);
  return true;
}

static void TakeWrittenFields(
    const ModuleItem* item,
    const std::unordered_map<std::string_view, std::vector<Expr*>>&
        td_array_dims,
    const GenBlockConsts& gen_loop_consts, RtlirVariable& var) {
  var.loc = item->loc;
  var.elem_type_kind = item->data_type.kind;
  var.element.type_is_unpacked_array =
      item->data_type.kind == DataTypeKind::kNamed &&
      td_array_dims.contains(item->data_type.type_name);
  var.init_expr = item->init_expr;
  var.gen_block_consts = gen_loop_consts;
}

static void ResolveOrReportClassScopedDeclType(ModuleItem* item,
                                               const TypedefMap& typedefs,
                                               const CompilationUnit* unit,
                                               DiagEngine& diag) {
  const ModuleItem* td =
      ResolveClassScopedDeclType(item->data_type, typedefs, unit);
  if (td != nullptr) {
    item->unpacked_dims.insert(item->unpacked_dims.end(),
                               td->unpacked_dims.begin(),
                               td->unpacked_dims.end());
  }
  ReportUnresolvedClassScopedType(item->data_type, item->loc, typedefs, unit,
                                  diag);
}

std::string_view Elaborator::ResolveVarDeclTypeRefs(ModuleItem* item,
                                                    RtlirModule* mod) {
  std::vector<Expr*> taken_dims =
      TypeRefUnpackedDims(item->data_type.type_ref_expr, mod);
  std::string_view adopted_enumeration =
      ResolveTypeRef(item->data_type, item->loc, mod);
  item->unpacked_dims.insert(item->unpacked_dims.end(), taken_dims.begin(),
                             taken_dims.end());
  ResolveTypeRefIndexDims(
      item->unpacked_dims,
      [&](DataType& type) { ResolveTypeRef(type, item->loc, mod); }, arena_);
  return adopted_enumeration;
}

void Elaborator::ReportSpecializationErrors(const DataType& written,
                                            SourceLoc loc,
                                            const RtlirModule* mod) {
  ReportSpecializationBindingErrors(written, loc,
                                    {typedefs_, unit_, class_names_}, diag_);
  if (written.type_params.empty()) return;
  const TypeShapeTables kTables{typedefs_, td_array_dims_, class_names_};
  ReportSpecializationValueTypes(written, {*mod, gen_prefix_},
                                 {kTables, BuildParamScope(mod), unit_}, diag_);
}

void Elaborator::ElaborateVarDecl(ModuleItem* item, RtlirModule* mod) {
  if (item->is_genvar) return;

  ReportUndeclaredTypeName(item);
  ReportSpecializationErrors(item->data_type, item->loc, mod);

  std::string_view adopted_enumeration = ResolveVarDeclTypeRefs(item, mod);

  SpecializeClassScopedTypedef(item, unit_, BuildParamScope(mod), typedefs_,
                               arena_);

  std::string_view adopted_array_typedef =
      AdoptTypedefArrayDims(item, typedefs_, td_array_dims_);

  ResolveDeclaredTypeName(item, unit_, typedefs_, class_names_, diag_);

  ResolveOrReportClassScopedDeclType(item, typedefs_, unit_, diag_);

  if (ElaborateUserNettypeNet(item, mod)) return;

  if (item->is_automatic) {
    diag_.Error(item->loc,
                "automatic lifetime is not allowed on module-level variables",
                Subclause("6.21"));
  }
  CheckDeclRedeclaration(
      item, {item->data_type, typedefs_},
      {ansi_port_names_, non_ansi_complete_ports_, non_ansi_partial_ports_,
       declared_names_, ScopedName(item->name),
       DeclaresNetOrVariable(item->name)},
      "variable", diag_);

  RegisterVarDeclNames(item,
                       {const_names_, const_var_names_, var_types_,
                        scalar_var_names_, real_var_names_, packed_array_vars_,
                        var_named_types_, var_select_shapes_},
                       typedefs_, diag_);
  RegisterVirtualInterfaceVarDecl(
      item,
      item->data_type.kind == DataTypeKind::kVirtualInterface
          ? FindModuleInScope(item->data_type.type_name)
          : nullptr,
      {vi_var_interface_types_, vi_var_modports_, vi_var_param_values_},
      BuildParamScope(mod), diag_);

  RtlirVariable var;
  var.name = ScopedName(item->name);
  TakeWrittenFields(item, td_array_dims_, gen_loop_consts_, var);
  var.gen_block_prefix = InternedGenPrefix();
  SizeClassHandleMembers(item->data_type, typedefs_, class_names_);
  var.width = EvalTypeWidth(item->data_type, typedefs_, BuildParamScope(mod));
  ValidatePackedDimRange(item->data_type, item->loc);
  SetVariableKindFlags(item, var, typedefs_);
  var.is_signed =
      ReconcilePartialPort(item->name, IsSignedType(item->data_type, typedefs_),
                           NetType::kNone, mod);

  if (item->init_expr) var_init_names_.insert(var.name);

  SetVariableTypeInfo(item, var, BuildParamScope(mod));
  NameAdoptedArrayTypedef(item, adopted_array_typedef, var);
  if (!adopted_enumeration.empty()) var.enum_type_name = adopted_enumeration;
  BindCovergroupVariable(*item, var, mod, unit_, arena_);

  ElaborateUnpackedDims(
      item, td_array_dims_,
      {{typedefs_, class_names_}, BuildParamScope(mod), diag_, item->loc}, var);
  ValidateUnpackedDimRange(item->unpacked_dims, item->loc);

  TrackVarArrayInfo(item, var, BuildParamScope(mod), var_array_info_);

  var.attrs = ResolveAttributes(item->attrs, diag_, BuildParamScope(mod));
  bool writes_its_type =
      adopted_array_typedef.empty() && adopted_enumeration.empty();
  ValidateVarDeclTypes(item, BuildParamScope(mod), writes_its_type);
  if (writes_its_type) EmitBareEnumMembers(item, mod);
  mod->variables.push_back(var);
  ValidateArrayInitPattern(item);
  ValidateStructInitPattern(item);
  TrackEnumVariable(item);
}

}  // namespace delta
