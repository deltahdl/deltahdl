#include "simulator/vpi_design_attach_vars.h"

#include <string>

#include "elaborator/net_data_type.h"
#include "elaborator/rtlir.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_declared_shape.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_packed_arrays.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers2.h"
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
  WalkInstancePaths(
      &design, [&](const RtlirModule* mod, const std::string& prefix) {
        for (const RtlirVariable& var : mod->variables) {
          if (var.init_expr == nullptr) continue;
          VpiObject* obj =
              FindObjectForFlatName(objects, VpiFlatName(prefix, var.name));
          if (obj == nullptr) continue;
          obj->decl_facts.init_expr =
              VpiInstanceExpression(var.init_expr, objects, prefix, ctx, build);
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

}  // namespace delta
