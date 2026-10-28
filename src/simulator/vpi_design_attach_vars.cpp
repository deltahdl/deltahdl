#include "simulator/vpi_design_attach_vars.h"

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

// §6.11: the integer types, which §37.17 detail 20 makes vectors.
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

// A bit or logic type, or one written with no type at all, which is logic.
bool IsBitOrLogicKind(DataTypeKind kind) {
  return kind == DataTypeKind::kLogic || kind == DataTypeKind::kBit ||
         kind == DataTypeKind::kReg || kind == DataTypeKind::kImplicit;
}

// §37.17 detail 20: what a declaration of `declared`, of the kind `kind`,
// tells VpiVariableScalar and VpiVariableVector of an object of `type` -- its
// packed dimension and packedness, an enum's base type (int where the enum
// names none) and an array's element type.
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

// The same for the variable `var`, an object of `type`.
VpiScalarVectorQuery ScalarVectorQueryOf(int type, const RtlirVariable& var) {
  return DeclaredShapeQuery(type, var.dtype, var.decl_kind);
}

// §37.17 details 9 and 21: an array var's kind, and its size -- for a fixed
// array the number of variables along its leftmost dimension, for the others
// the run's store whose current count is answered when asked.
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

// §37.17 and §37.26: a struct or union var, one named through a typedef told
// its kind as one written out is (VpiVariableObjectKind), is packed or not as
// the run's layout of it says, and an unpacked one's size is its number of
// fields (detail 9). Every struct or union var has that layout: the elaborator
// gives an aggregate declaration its type and Lowerer::LowerVar registers the
// layout under the variable's name (RegisterAggregateLayout).
void RecordAggregateFacts(VpiObject* obj, const std::string& key,
                          SimContext& ctx) {
  const StructTypeInfo* info = ctx.GetVariableStructType(key);
  if (info == nullptr) return;
  if (obj->type != vpiStructVar && obj->type != vpiUnionVar) return;
  // §37.26: whether it is packed, which vpiPacked reports and which leaves
  // its value accessible (detail 1).
  obj->packed = info->is_packed;
  if (!info->is_packed) obj->size = static_cast<int>(info->fields.size());
}

// §37.17: the facts a variable's object answers from its declaration.
void RecordVariableFacts(VpiObject* obj, const RtlirVariable& var,
                         const std::string& key, SimContext& ctx) {
  RecordAggregateFacts(obj, key, ctx);
  // §37.26: whether the union was declared tagged or soft.
  if (obj->type == vpiUnionVar && var.dtype != nullptr) {
    obj->tagged = var.dtype->is_tagged;
    obj->soft = var.dtype->is_soft;
  }
  obj->decl_signed = var.is_signed;
  const VpiScalarVectorQuery kQuery = ScalarVectorQueryOf(obj->type, var);
  obj->decl_scalar = VpiVariableScalar(kQuery);
  obj->decl_vector = VpiVariableVector(kQuery);
  RecordArrayFacts(obj, var, key, ctx);
}

// §37.17 with Table 36-10: the object kind of the variable the declaration
// `item` of the package named `package`, or of the compilation unit where that
// is empty, makes: the kind of the type it is written with, through a typedef
// name the kind at the end of its chain resolved in that scope or in the
// package written before the name (§26.3), and for an unpacked array one kind
// whatever it holds, an array of events apart (§37.27).
int ScopeVariableKind(const ModuleItem& item, std::string_view package,
                      const RtlirDesign& design) {
  const DataType& type = item.data_type;
  const int kKind = type.kind == DataTypeKind::kNamed
                        ? VpiScopedTypeVariableKind(design, package, type)
                        : VpiDataTypeVariableKind(type.kind);
  if (item.unpacked_dims.empty()) return kKind;
  return kKind == vpiNamedEvent ? vpiNamedEventArray : vpiRegArray;
}

// §37.17 detail 20 with §6.18: the shape the package's or unit's variable
// `obj` was declared with, written as `type` in the package named `package`,
// empty for the unit: signed as the run's storage of it is, which follows a
// typedef name to its type (§6.11), and a scalar or a vector as the type a
// typedef name stands for says, followed through the chain to the first
// declaration writing a packed dimension (§7.4.4). A name written alone is the
// package's own, which the run keys `p::t`, and the unit's typedef is keyed by
// its bare name.
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

// §37.17 details 9 and 21: the kind of array the package's or unit's array var
// `obj`, keyed `key`, is by the first unpacked dimension `dim` it was declared
// with, read in the scope named `scope`, with the run's store of its elements
// (lowerer_package_data.cpp): a dynamic array's queue (§7.5), a queue's
// (§7.10) and an associative array's object (§7.8), and for a fixed-size
// array the number of variables along that dimension.
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

// A package, or the compilation unit, as the scope of the variables it
// declares (§26.2, §3.12.1): the items it declares, the name the run keys
// their storage under, and the name of the package a typedef name they are
// written with resolves in, empty for the unit.
struct DeclaringScope {
  const std::vector<ModuleItem*>& items;
  std::string_view name;
  std::string_view package;
};

// The kind of each variable `scope` declares and the facts read off the
// declaration with it, as a module's variable is told them: whether it is
// constant (§6.20.6), the interface a virtual interface var's clocking blocks
// are found in (§25.9), whether it is a modport, and for a structure or union
// whether it is packed, from the layout the run `ctx` holds under the
// variable's key (§37.26).
void RecordScopeVariableKinds(const DeclaringScope& scope,
                              const RtlirDesign& design,
                              const VpiObjectMap& objects, SimContext& ctx) {
  for (const ModuleItem* item : scope.items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    const std::string kKey =
        std::string(scope.name) + "." + std::string(item->name);
    // The run stores every variable a package or a unit declares under this
    // key (lowerer_package_data.cpp), and VpiContext::Attach makes an object
    // for each, an import's key being the importing instance's own spelling
    // rather than the package's.
    VpiHandle obj = FindObjectForFlatName(objects, kKey);
    const DataType& type = item->data_type;
    obj->type = ScopeVariableKind(*item, scope.package, design);
    obj->decl_facts.constant_variable = type.is_const;
    obj->decl_facts.vif_interface = VpiVirtualInterfaceOf(design, &type);
    obj->is_modport = !type.modport_name.empty();
    RecordAggregateFacts(obj, kKey, ctx);
    RecordScopeDeclaredShape(*obj, type, scope.package, ctx);
    if (!item->unpacked_dims.empty()) {
      RecordScopeArrayFacts(*obj, item->unpacked_dims.front(), kKey, scope.name,
                            ctx);
    }
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
  // §37.17: vpiSigned, vpiScalar, vpiVector, vpiArrayType and vpiSize are what
  // a variable's declaration makes of it. The object a run built carried none
  // of them: each answered FALSE, 0 or the bit width of the storage. The pass
  // runs from VpiContext::Attach, which has set the run it reads by then.
  if (design == nullptr) return;
  SimContext& ctx = *sim_ctx_;
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        for (const RtlirVariable& var : mod->variables) {
          const std::string kKey = VpiFlatName(prefix, var.name);
          VpiHandle obj = FindObjectForFlatName(object_map_, kKey);
          if (obj != nullptr) RecordVariableFacts(obj, var, kKey, ctx);
        }
      });
}

void AttachVariableInitializers(const RtlirDesign& design,
                                const VpiObjectMap& objects, SimContext& ctx,
                                const VpiAttachBuild& build) {
  // An initializer, written outside every procedure and generate block, finds
  // the instance's declarations, then those of the packages its module
  // imports (§26.3) and of the compilation unit it was declared in (§3.12.1).
  static const GenBlockPrefixes kNoGenBlocks;
  WalkInstanceObjects(&design, objects,
                      [&](const RtlirModule* mod, const std::string& prefix,
                          const VpiObject* instance) {
                        for (const RtlirVariable& var : mod->variables) {
                          if (var.init_expr == nullptr) continue;
                          VpiObject* obj = FindObjectForFlatName(
                              objects, VpiFlatName(prefix, var.name));
                          if (obj == nullptr) continue;
                          obj->decl_facts.init_expr = VpiGenBlockExpression(
                              var.init_expr,
                              {objects, prefix, kNoGenBlocks, nullptr, nullptr,
                               nullptr, mod, instance},
                              ctx, build);
                        }
                      });
}

int VpiVariableObjectKind(const RtlirVariable& var, const RtlirDesign& design,
                          const RtlirModule& mod) {
  // §37.62 (figure): the object an event statement triggers is a named event,
  // and §37.27 draws the array of them beside it. A named event is not a
  // variable holding a value, so Table 36-10's rule that an unpacked array of
  // variables is one vpiRegArray object says nothing about it and the event
  // kinds answer ahead of that rule. Without this an event declaration's object
  // was a reg, so the arrow §37.62 draws from an event statement reached an
  // object of a kind the figure has no box for.
  if (var.is_event) {
    return var.num_unpacked_dims > 0 ? vpiNamedEventArray : vpiNamedEvent;
  }
  // §37.17 detail 1 with Table 36-10: an array of variables is one array var,
  // whether its unpacked dimension is fixed or a queue's, a dynamic array's or
  // an associative array's.
  if (var.num_unpacked_dims > 0 || var.is_queue || var.is_dynamic ||
      var.is_assoc) {
    return vpiRegArray;
  }
  // A name declared through a typedef reports kNamed, so the flags the
  // elaborator resolved through the typedef answer first for the kinds that
  // have one.
  // §37.33: a variable declared with a class type is the clause's "class var",
  // the object every rule of the subclause is written about. A class type is
  // named rather than a DataTypeKind of its own, so decl_kind leaves it in the
  // kNamed default and the variable was stamped vpiReg: a design's class
  // variables were class vars to nothing, vpiObjId and vpiClassObj answered for
  // none of them, and a vpiClassVar iteration reached none.
  if (!var.class_type_name.empty()) return vpiClassVar;
  if (VpiVariableIsPackedArray(var)) return vpiPackedArrayVar;
  if (var.decl_kind == DataTypeKind::kShortreal) return vpiShortRealVar;
  if (var.is_real) return vpiRealVar;
  if (var.is_string) return vpiStringVar;
  if (var.is_chandle) return vpiChandleVar;
  // A variable declared with an enum typedef reports kNamed; the enum it names
  // makes it an enum var all the same.
  if (!var.enum_type_name.empty()) return vpiEnumVar;
  // A typedef name no fact above claims, an int's, a struct's or a virtual
  // interface's among them, is told through the kind the design records at
  // the end of its chain, as a task's or function's variable is
  // (DeclaredVariableKind), under `p::t` for one a package declares (§26.3).
  if (var.decl_kind == DataTypeKind::kNamed) {
    return VpiNamedTypeVariableKind(design, mod,
                                    NamedTypeKey(*var.written_type));
  }
  // §37.17 detail 19: a logic var and a reg are the same object kind, and it
  // is what a variable the clause draws no separate box for carries.
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
