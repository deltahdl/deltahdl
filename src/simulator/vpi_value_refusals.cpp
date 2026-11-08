#include "simulator/vpi_value_refusals.h"

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

void RecordVpiError(s_vpi_error_info& error, const char* message) {
  error.state = kVpiPLI;
  error.level = kVpiError;
  error.message = VpiText(message);
}

bool IsPutValueTargetType(int type) {
  if (VpiIsNetsType(type) || VpiIsVariablesType(type) ||
      VpiObjectIsPrimitive(type)) {
    return true;
  }
  return type == vpiVarSelect || type == vpiNamedEvent ||
         type == vpiSysFuncCall || type == vpiSchedEvent;
}

}  // namespace

bool VpiGetValueIsRefused(VpiHandle obj, const s_vpi_value& value,
                          s_vpi_error_info& error) {
  if (obj->parent && obj->parent->type == vpiClassDefn &&
      VpiIsClassMemberValueType(obj->type)) {
    RecordVpiError(
        error,
        "vpi_get_value(): a variable or event handle obtained from a "
        "class definition handle has no accessible value");
    return true;
  }
  if (VpiIsVariablesType(obj->type) &&
      !VpiVariableHasValueProperty(obj->type, true)) {
    RecordVpiError(error,
                   "vpi_get_value(): an array, class or virtual interface "
                   "variable has no value");
    return true;
  }
  if (VpiIsEntireUnpackedStructOrUnion(obj->type, obj->packed)) {
    RecordVpiError(error,
                   "vpi_get_value(): the value of an entire unpacked structure "
                   "or union cannot be accessed");
    return true;
  }
  if (obj->type == vpiTableEntry && value.format != kVpiStringVal &&
      value.format != kVpiVectorVal) {
    RecordVpiError(
        error,
        "vpi_get_value(): a table entry value is available only as a "
        "string or a vector");
    return true;
  }
  return false;
}

bool VpiPutValueTargetIsRejected(VpiHandle obj, s_vpi_error_info& error) {
  if (obj->parent && obj->parent->type == vpiClassDefn &&
      VpiIsClassMemberValueType(obj->type)) {
    RecordVpiError(
        error,
        "vpi_put_value(): a variable or event handle obtained from a "
        "class definition handle has no accessible value");
    return true;
  }

  if (VpiIsVariablesType(obj->type) &&
      !VpiVariableHasValueProperty(obj->type, true)) {
    RecordVpiError(error,
                   "vpi_put_value(): an array, class or virtual interface "
                   "variable has no value");
    return true;
  }

  if (VpiIsEntireUnpackedStructOrUnion(obj->type, obj->packed)) {
    RecordVpiError(error,
                   "vpi_put_value(): the value of an entire unpacked structure "
                   "or union cannot be accessed");
    return true;
  }

  if (VpiObjectIsPrimitive(obj->type) && obj->prim_type != vpiSeqPrim) {
    RecordVpiError(
        error,
        "vpi_put_value(): only a sequential UDP primitive may be written");
    return true;
  }

  if (VpiNetTypeOf(obj) == vpiNettypeNetSelect) {
    RecordVpiError(error,
                   "vpi_put_value(): a subelement of a user-defined nettype "
                   "net cannot be written");
    return true;
  }

  for (const VpiObject* index : obj->index_expressions) {
    if (VpiExpressionHasSideEffects(index)) {
      RecordVpiError(
          error,
          "vpi_put_value(): an index expression with side effects is "
          "not allowed");
      return true;
    }
  }

  if (!IsPutValueTargetType(obj->type)) {
    RecordVpiError(error,
                   "vpi_put_value(): a value can be put only to a net, a "
                   "variable, a variable select, a named event, a system "
                   "function call, a sequential UDP or a scheduled event");
    return true;
  }
  return false;
}

}  // namespace delta
