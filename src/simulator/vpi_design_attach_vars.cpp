#include "simulator/vpi_design_attach_vars.h"

#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/packed_range.h"
#include "elaborator/net_data_type.h"
#include "elaborator/queue_dim.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/unit_scope_items.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_declared_shape.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_packed_arrays.h"
#include "simulator/vpi_design_prefixed_refs.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_named_type_kinds.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

bool IsIntegerKind(DataTypeKind kind) {
  switch (kind) {
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

bool IsBitOrLogicKind(DataTypeKind kind) {
  return kind == DataTypeKind::kLogic || kind == DataTypeKind::kBit ||
         kind == DataTypeKind::kReg || kind == DataTypeKind::kImplicit;
}

VpiScalarVectorQuery DeclaredShapeQuery(int type, const DataType* declared,
                                        DataTypeKind kind) {
  VpiScalarVectorQuery query;
  query.var_type = type;
  query.has_packed_dimension =
      declared != nullptr && declared->packed_dim_left != nullptr;
  query.packed = declared != nullptr && declared->is_packed;
  const bool kBaseIsBitOrLogic =
      declared != nullptr &&
      declared->enum_base_kind != DataTypeKind::kImplicit &&
      IsBitOrLogicKind(declared->enum_base_kind);
  query.base_is_scalar = kBaseIsBitOrLogic && !query.has_packed_dimension;
  query.base_is_vector = !query.base_is_scalar;
  query.element_is_vector = query.has_packed_dimension || IsIntegerKind(kind);
  query.element_is_scalar = !query.element_is_vector && IsBitOrLogicKind(kind);
  return query;
}

VpiScalarVectorQuery ScalarVectorQueryOf(int type, const RtlirVariable& var) {
  return DeclaredShapeQuery(type, var.dtype, var.decl_kind);
}

void RecordArrayFacts(VpiObject* obj, const RtlirVariable& var,
                      const std::string& key, SimContext& ctx) {
  if (var.is_queue || var.is_dynamic) {
    obj->array_type = var.is_queue ? vpiQueueArray : vpiDynamicArray;
    obj->queue = ctx.FindQueue(key);
  } else if (var.is_assoc) {
    obj->array_type = vpiAssocArray;
    obj->assoc = ctx.FindAssocArray(key);
  } else if (var.num_unpacked_dims > 0) {
    obj->array_type = vpiStaticArray;
    obj->size = static_cast<int>(var.unpacked_dim_sizes.empty()
                                     ? var.unpacked_size
                                     : var.unpacked_dim_sizes.front());
  }
}

void RecordAggregateFacts(VpiObject* obj, const std::string& key,
                          SimContext& ctx) {
  const StructTypeInfo* info = ctx.GetVariableStructType(key);
  if (info == nullptr) return;
  if (obj->type != vpiStructVar && obj->type != vpiUnionVar) return;
  obj->packed = info->is_packed;
  if (!info->is_packed) obj->size = static_cast<int>(info->fields.size());
}

void RecordVariableFacts(VpiObject* obj, const RtlirVariable& var,
                         const std::string& key, SimContext& ctx) {
  RecordAggregateFacts(obj, key, ctx);
  if (obj->type == vpiUnionVar) {
    obj->tagged = var.dtype->is_tagged;
    obj->soft = var.dtype->is_soft;
  }
  obj->decl_signed = var.is_signed;
  const VpiScalarVectorQuery kQuery = ScalarVectorQueryOf(obj->type, var);
  obj->decl_scalar = VpiVariableScalar(kQuery);
  obj->decl_vector = VpiVariableVector(kQuery);
  RecordArrayFacts(obj, var, key, ctx);
}

int ScopeVariableKind(const ModuleItem& item, std::string_view package,
                      const RtlirDesign& design) {
  const DataType& type = item.data_type;
  const int kKind = type.kind == DataTypeKind::kNamed
                        ? VpiScopedTypeVariableKind(design, package, type)
                        : VpiDataTypeVariableKind(type.kind);
  if (item.unpacked_dims.empty()) return kKind;
  return kKind == vpiNamedEvent ? vpiNamedEventArray : vpiRegArray;
}

void RecordScopeDeclaredShape(VpiObject& obj, const DataType& type,
                              std::string_view package, SimContext& ctx) {
  obj.decl_signed = obj.var->is_signed;
  DataType written = type;
  if (written.scope_name.empty()) written.scope_name = package;
  const DataTypeKind kKind = type.kind == DataTypeKind::kNamed
                                 ? ctx.FindTypeKind(NamedTypeKey(written))
                                 : type.kind;
  const VpiScalarVectorQuery kQuery =
      DeclaredShapeQuery(obj.type, ctx.PackedTypeBehind(written), kKind);
  obj.decl_scalar = VpiVariableScalar(kQuery);
  obj.decl_vector = VpiVariableVector(kQuery);
}

void RecordScopeArrayFacts(VpiObject& obj, const Expr* dim,
                           const std::string& key, std::string_view scope,
                           SimContext& ctx) {
  ctx.PushScope(scope);
  if (dim == nullptr || IsQueueDim(dim)) {
    obj.array_type = dim == nullptr ? vpiDynamicArray : vpiQueueArray;
    obj.queue = ctx.FindQueue(key);
  } else if (IsAssocIndexDim(dim, ctx)) {
    obj.array_type = vpiAssocArray;
    obj.assoc = ctx.FindAssocArray(key);
  } else {
    const PackedRange kRange =
        WrittenUnpackedDim(dim, ctx).value_or(PackedRange{});
    obj.array_type = vpiStaticArray;
    obj.size = static_cast<int>(kRange.HighIndex() - kRange.LowIndex() + 1);
  }
  ctx.PopScope();
}

struct DeclaringScope {
  const std::vector<ModuleItem*>& items;
  std::string_view name;
  std::string_view package;
};

void RecordScopeVariableKinds(const DeclaringScope& scope,
                              const RtlirDesign& design,
                              const VpiObjectMap& objects, SimContext& ctx) {
  for (const ModuleItem* item : scope.items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    const std::string kKey =
        std::string(scope.name) + "." + std::string(item->name);
    VpiHandle obj = FindObjectForFlatName(objects, kKey);
    const DataType& type = item->data_type;
    obj->type = ScopeVariableKind(*item, scope.package, design);
    obj->decl_facts.constant_variable = type.is_const;
    obj->decl_facts.vif_interface =
        VpiVirtualInterfaceOf(design, &type, nullptr);
    obj->is_modport = !type.modport_name.empty();
    RecordAggregateFacts(obj, kKey, ctx);
    RecordScopeDeclaredShape(*obj, type, scope.package, ctx);
    if (!item->unpacked_dims.empty()) {
      RecordScopeArrayFacts(*obj, item->unpacked_dims.front(), kKey, scope.name,
                            ctx);
    }
  }
}

void ForEachVariableObject(
    const RtlirModule& mod, const std::string& prefix,
    const VpiObjectMap& objects,
    const std::function<void(const RtlirVariable&, VpiObject&)>& visit) {
  for (const RtlirVariable& var : mod.variables) {
    VpiObject* obj =
        FindObjectForFlatName(objects, VpiFlatName(prefix, var.name));
    if (obj != nullptr) visit(var, *obj);
  }
}

}  // namespace

void VpiRecordDeclaredShape(VpiObject* var, const DataType& type) {
  var->decl_signed = type.is_signed;
  const VpiScalarVectorQuery kQuery =
      DeclaredShapeQuery(var->type, &type, type.kind);
  var->decl_scalar = VpiVariableScalar(kQuery);
  var->decl_vector = VpiVariableVector(kQuery);
}

void VpiContext::AttachVariableFacts(const RtlirDesign* design) {
  if (design == nullptr) return;
  SimContext& ctx = *sim_ctx_;
  WalkInstancePaths(design, [&](const RtlirModule* mod,
                                const std::string& prefix) {
    ForEachVariableObject(*mod, prefix, object_map_,
                          [&](const RtlirVariable& var, VpiObject& obj) {
                            RecordVariableFacts(
                                &obj, var, VpiFlatName(prefix, var.name), ctx);
                          });
  });
}

void AttachVariableInitializers(const RtlirDesign& design,
                                const VpiObjectMap& objects, SimContext& ctx,
                                const VpiAttachBuild& build) {
  static const GenBlockPrefixes kNoGenBlocks;
  WalkInstanceObjects(&design, objects,
                      [&](const RtlirModule* mod, const std::string& prefix,
                          const VpiObject* instance) {
                        ForEachVariableObject(
                            *mod, prefix, objects,
                            [&](const RtlirVariable& var, VpiObject& obj) {
                              if (var.init_expr == nullptr) return;
                              obj.decl_facts.init_expr = VpiGenBlockExpression(
                                  var.init_expr,
                                  {objects, prefix, kNoGenBlocks, nullptr,
                                   nullptr, nullptr, mod, instance},
                                  ctx, build);
                            });
                      });
}

int VpiVariableObjectKind(const RtlirVariable& var, const RtlirDesign& design,
                          const RtlirModule& mod) {
  if (var.is_event) {
    return var.num_unpacked_dims > 0 ? vpiNamedEventArray : vpiNamedEvent;
  }
  if (var.num_unpacked_dims > 0) return vpiRegArray;
  if (!var.class_type_name.empty()) return vpiClassVar;
  if (VpiVariableIsPackedArray(var)) return vpiPackedArrayVar;
  if (var.decl_kind == DataTypeKind::kShortreal) return vpiShortRealVar;
  if (var.is_real) return vpiRealVar;
  if (var.is_string) return vpiStringVar;
  if (var.is_chandle) return vpiChandleVar;
  if (!var.enum_type_name.empty()) return vpiEnumVar;
  if (var.decl_kind == DataTypeKind::kNamed) {
    return VpiNamedTypeVariableKind(design, mod,
                                    NamedTypeKey(*var.written_type));
  }
  return VpiDataTypeVariableKind(var.decl_kind);
}

void VpiRecordScopeVariableKinds(const RtlirDesign& design,
                                 const VpiObjectMap& objects, SimContext& ctx) {
  for (const PackageDecl* pkg : design.packages) {
    RecordScopeVariableKinds({pkg->items, pkg->name, pkg->name}, design,
                             objects, ctx);
  }
  ForEachUnitScope(&design, ctx.GetArena(),
                   [&](const CompilationUnit& unit, std::string_view scope) {
                     RecordScopeVariableKinds({unit.cu_items, scope, ""},
                                              design, objects, ctx);
                   });
}

}  // namespace delta
