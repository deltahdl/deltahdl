#include <string>

#include "elaborator/rtlir.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"

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

// §37.17 detail 20: what the declaration of `var`, an object of `type`, tells
// VpiVariableScalar and VpiVariableVector -- its packed dimension and
// packedness, an enum's base type (int where the enum names none) and an
// array's element type.
VpiScalarVectorQuery ScalarVectorQueryOf(int type, const RtlirVariable& var) {
  VpiScalarVectorQuery query;
  query.var_type = type;
  const DataType* declared = var.dtype;
  query.has_packed_dimension =
      declared != nullptr && declared->packed_dim_left != nullptr;
  query.packed = declared != nullptr && declared->is_packed;
  const bool kBaseIsBitOrLogic =
      declared != nullptr &&
      declared->enum_base_kind != DataTypeKind::kImplicit &&
      IsBitOrLogicKind(declared->enum_base_kind);
  query.base_is_scalar = kBaseIsBitOrLogic && !query.has_packed_dimension;
  query.base_is_vector = !query.base_is_scalar;
  query.element_is_vector =
      query.has_packed_dimension || IsIntegerKind(var.decl_kind);
  query.element_is_scalar =
      !query.element_is_vector && IsBitOrLogicKind(var.decl_kind);
  return query;
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

// §37.17 and §37.26: a variable whose type is a struct or union named through
// a typedef reports kNamed and was stamped a reg; the run's layout of it says
// which of the two it is, and an unpacked one's size is its number of fields
// (detail 9). Every struct or union var has that layout: the elaborator gives
// an aggregate declaration its type and Lowerer::LowerVar registers the
// layout under the variable's name (RegisterAggregateLayout).
void RecordAggregateFacts(VpiObject* obj, const std::string& key,
                          SimContext& ctx) {
  const StructTypeInfo* info = ctx.GetVariableStructType(key);
  if (info == nullptr) return;
  if (obj->type == kVpiReg) {
    obj->type = info->is_union ? vpiUnionVar : vpiStructVar;
  }
  if (obj->type != vpiStructVar && obj->type != vpiUnionVar) return;
  if (!info->is_packed) obj->size = static_cast<int>(info->fields.size());
}

// §37.17: the facts a variable's object answers from its declaration.
void RecordVariableFacts(VpiObject* obj, const RtlirVariable& var,
                         const std::string& key, SimContext& ctx) {
  RecordAggregateFacts(obj, key, ctx);
  obj->decl_signed = var.is_signed;
  const VpiScalarVectorQuery kQuery = ScalarVectorQueryOf(obj->type, var);
  obj->decl_scalar = VpiVariableScalar(kQuery);
  obj->decl_vector = VpiVariableVector(kQuery);
  RecordArrayFacts(obj, var, key, ctx);
}

}  // namespace

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

}  // namespace delta
