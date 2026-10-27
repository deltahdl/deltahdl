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

// §38.34: whether vpi_put_value() can be applied to an object of kind `type`:
// a net, a variable (a memory word being a reg, §37.20 detail 1), a variable
// select, which is a var select (§37.19), a named event, a system function
// call, a primitive, of which a sequential UDP is the one a value is put to
// (§37.35 detail 2), or a scheduled event. A bit select, a part select and an
// indexed part select are not among them: each is an expression (§37.58,
// §37.59) holding no storage of its own, the bits of a vector a put writes
// being a net bit, a var bit or a slice of the vector's own kind. Nor is a
// system task call: a task returns no value (§36.5), so its call has none for
// a put to write.
bool IsPutValueTargetType(int type) {
  if (VpiIsNetsType(type) || VpiIsVariablesType(type) ||
      VpiObjectIsPrimitive(type)) {
    return true;
  }
  return type == vpiVarSelect || type == vpiNamedEvent ||
         type == vpiSysFuncCall || type == vpiSchedEvent;
}

}  // namespace

// Applies the §37.31/§37.26/§37.36 read-side restrictions. Returns true (with
// last_error recorded) when the read must be refused and the value buffer left
// untouched.
bool VpiGetValueIsRefused(VpiHandle obj, const s_vpi_value& value,
                          s_vpi_error_info& error) {
  // §37.31 detail 2: vpi_get_value() is not allowed for variable and event
  // handles obtained from a class defn handle. Such a handle denotes a class
  // member rather than a free-standing object, so the read is refused, an error
  // is recorded, and the caller's value buffer is left untouched.
  if (obj->parent && obj->parent->type == vpiClassDefn &&
      VpiIsClassMemberValueType(obj->type)) {
    RecordVpiError(
        error,
        "vpi_get_value(): a variable or event handle obtained from a "
        "class definition handle has no accessible value");
    return true;
  }
  // §37.17 detail 11: an array var, a class var and a virtual interface var
  // have no value property, so reading one is refused as well.
  if (VpiIsVariablesType(obj->type) &&
      !VpiVariableHasValueProperty(obj->type, true)) {
    RecordVpiError(error,
                   "vpi_get_value(): an array, class or virtual interface "
                   "variable has no value");
    return true;
  }
  // §37.26 detail 1: the value of an entire unpacked structure or unpacked
  // union is not accessible through vpi_get_value(). Such an aggregate holds no
  // single scalar or vector value to hand back, so the read is refused, an
  // error is recorded, and the caller's value buffer is left untouched. A
  // packed struct/union is excluded by the helper and reads normally.
  if (VpiIsEntireUnpackedStructOrUnion(obj->type, obj->packed)) {
    RecordVpiError(error,
                   "vpi_get_value(): the value of an entire unpacked structure "
                   "or union cannot be accessed");
    return true;
  }
  // §37.36 detail 1: only a string value (the decompiled symbol row) and a
  // vector value (its symbols, two bytes each, §38.15) shall be obtained for a
  // table entry object through vpi_get_value(). Any other requested format is
  // refused, an error is recorded, and the caller's value buffer is left
  // untouched.
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

// Applies the §37.31/§37.26/§37.35/§37.3.5 target-kind restrictions, and
// §38.34's list of the kinds of object the routine applies to, that hold
// regardless of the requested delay mode. Returns true (with error recorded)
// when the put must be refused and the target left unchanged.
bool VpiPutValueTargetIsRejected(VpiHandle obj, s_vpi_error_info& error) {
  // §37.31 detail 2: vpi_put_value() is not allowed for variable and event
  // handles obtained from a class defn handle, the write side of the same
  // restriction vpi_get_value() observes. The put is rejected, an error is
  // recorded, and the member is left unchanged.
  if (obj->parent && obj->parent->type == vpiClassDefn &&
      VpiIsClassMemberValueType(obj->type)) {
    RecordVpiError(
        error,
        "vpi_put_value(): a variable or event handle obtained from a "
        "class definition handle has no accessible value");
    return true;
  }

  // §37.17 detail 11: nor can an array var, a class var or a virtual
  // interface var, which have no value property.
  if (VpiIsVariablesType(obj->type) &&
      !VpiVariableHasValueProperty(obj->type, true)) {
    RecordVpiError(error,
                   "vpi_put_value(): an array, class or virtual interface "
                   "variable has no value");
    return true;
  }

  // §37.26 detail 1: an entire unpacked structure or union cannot be written
  // through vpi_put_value() any more than it can be read - it has no single
  // value to take the write. The put is rejected, an error is recorded, and the
  // aggregate is left unchanged. A packed struct/union is excluded by the
  // helper and is written through the normal path below.
  if (VpiIsEntireUnpackedStructOrUnion(obj->type, obj->packed)) {
    RecordVpiError(error,
                   "vpi_put_value(): the value of an entire unpacked structure "
                   "or union cannot be accessed");
    return true;
  }

  // §37.35 detail 2: among primitives, vpi_put_value() may be applied only to a
  // sequential UDP. Putting a value to any other primitive kind - a gate,
  // switch, combinational UDP, or a generic primitive - is not allowed, so the
  // put is rejected before any value is written. (The complementary delay-mode
  // restriction on a sequential UDP itself is checked further below.)
  if (VpiObjectIsPrimitive(obj->type) && obj->prim_type != vpiSeqPrim) {
    RecordVpiError(
        error,
        "vpi_put_value(): only a sequential UDP primitive may be written");
    return true;
  }

  // §38.34 with §6.6.7: a user-defined nettype's value is resolved whole, so
  // a subelement of a net of one takes no value of its own.
  if (VpiNetTypeOf(obj) == vpiNettypeNetSelect) {
    RecordVpiError(error,
                   "vpi_put_value(): a subelement of a user-defined nettype "
                   "net cannot be written");
    return true;
  }

  // §37.3.5: it is an error to apply vpi_put_value() to an object when any of
  // its index expressions has side effects (for instance my_array[i++] or
  // my_array[--i]). The write is rejected before any value is stored - an error
  // is recorded, the target is left unchanged, and the side-effecting index is
  // not evaluated.
  for (const VpiObject* index : obj->index_expressions) {
    if (VpiExpressionHasSideEffects(index)) {
      RecordVpiError(
          error,
          "vpi_put_value(): an index expression with side effects is "
          "not allowed");
      return true;
    }
  }

  // §38.34: nor can it be applied to an object of any kind the clause does not
  // list, a parameter, a specparam and a UDP table entry among those that hold
  // a value, and a bit select and a part select among the expressions that
  // select bits. The put is rejected, an error is recorded, and the object is
  // left unchanged.
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
