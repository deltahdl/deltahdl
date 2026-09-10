// §36.12.2: "In order to ease the transition to the latest VPI standard for
// older applications, capability shall be provided to emulate the incompatible
// VPI behaviors where they conflict with the current standard. This allows
// older VPI applications dependent on these behaviors to be run unmodified."
// §36.12.2.1's mechanism binds an application to one of those behaviors at
// compile time: selecting a version symbol retargets every standard entry point
// to that version's variant, and simulator/vpi_compatibility.h performs the
// retargeting. This file is what the retargeted names resolve to.
//
// Nothing defined them. An application that selected a mode had each of its
// calls renamed to a routine no translation unit declared or defined, so it did
// not compile and could not link, and the capability the clause requires was
// provided by the header's spelling alone.
//
// Each variant runs the current routine, and where §36.12.1's Table 36-10 marks
// a behavior as differing in that version and this simulator can act on it, the
// variant emulates the older one. The rows it can act on are 5, 6 and 7, all
// about which objects an iteration reaches; they are N for the IEEE 1364
// versions and Y for the IEEE 1800 ones, so the three 1364 variants of
// vpi_iterate filter and every other variant of every routine forwards.

#include <cstdarg>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"

// The reader §38.4's entry point starts an argument list for; the vpi_control
// variants below start their own and hand it to the same one.
PLI_INT32 VpiControlWithArgs(PLI_INT32 operation, va_list args);

namespace {

// §36.12.1 Table 36-10 row 5: "vpiVariables iterations include vpiReg and
// vpiRegArray" is Y in the IEEE 1800 standards and N in the IEEE 1364 ones, in
// which "vpiReg and vpiRegArray objects were excluded from vpiVariables
// iterations".
bool Vpi1364VariablesKeeps(int obj_type) {
  return obj_type != vpiReg && obj_type != vpiRegArray;
}

// §36.12.1 Table 36-10 rows 6 and 7: a vpiReg iteration on an array retrieves
// only the reg elements, and a vpiRegArray iteration reaches only arrays of
// regs - the two behaviors the rows say an IEEE 1364 application expects.
bool Vpi1364IterationKeeps(int type, delta::VpiHandle ref,
                           delta::VpiHandle object) {
  if (type == vpiVariables) return Vpi1364VariablesKeeps(object->type);
  if (type == vpiReg && ref != nullptr && delta::VpiIsArrayVarType(ref->type)) {
    return object->type == vpiReg;
  }
  if (type == vpiRegArray) return delta::VpiArrayVarIsMemory(object);
  return true;
}

// §36.12.1 Table 36-10: whether the version in force is one of the IEEE 1364
// standards, whose iterations rows 5, 6 and 7 differ in.
bool VpiModeIs1364(int mode) {
  return mode == vpiMode1364v1995 || mode == vpiMode1364v2001 ||
         mode == vpiMode1364v2005;
}

}  // namespace

namespace delta {

vpiHandle VpiIterateInCompatibilityMode(int type, VpiHandle ref, int mode) {
  // The iterator the current routine builds, with the objects an application
  // of `mode` does not expect dropped. An iteration left with nothing is the
  // NULL §38.23 gives one that reaches no object, so the emptied iterator is
  // released rather than handed back.
  vpiHandle iterator = delta::GetGlobalVpiContext().Iterate(type, ref);
  if (iterator == nullptr || !VpiModeIs1364(mode)) return iterator;
  std::vector<delta::VpiObject*> kept;
  for (auto* object : iterator->children) {
    if (Vpi1364IterationKeeps(type, ref, object)) kept.push_back(object);
  }
  iterator->children = kept;
  if (!iterator->children.empty()) return iterator;
  vpi_release_handle(iterator);
  return nullptr;
}

}  // namespace delta

// IEEE Std 1364-1995.
PLI_INT32 vpi_compare_objects_1364v1995(vpiHandle obj1, vpiHandle obj2) {
  return vpi_compare_objects(obj1, obj2);
}
PLI_INT32 vpi_get_1364v1995(PLI_INT32 property, vpiHandle obj) {
  return vpi_get(property, obj);
}
PLI_BYTE8* vpi_get_str_1364v1995(PLI_INT32 property, vpiHandle obj) {
  return vpi_get_str(property, obj);
}
void vpi_get_value_1364v1995(vpiHandle obj, s_vpi_value* value) {
  vpi_get_value(obj, value);
}
vpiHandle vpi_handle_1364v1995(PLI_INT32 type, vpiHandle ref) {
  return vpi_handle(type, ref);
}
vpiHandle vpi_handle_by_index_1364v1995(vpiHandle parent, PLI_INT32 index) {
  return vpi_handle_by_index(parent, index);
}
vpiHandle vpi_handle_by_multi_index_1364v1995(vpiHandle parent,
                                              PLI_INT32 num_index,
                                              PLI_INT32* index_array) {
  return vpi_handle_by_multi_index(parent, num_index, index_array);
}
vpiHandle vpi_handle_by_name_1364v1995(const char* name, vpiHandle scope) {
  return vpi_handle_by_name(name, scope);
}
vpiHandle vpi_handle_multi_1364v1995(PLI_INT32 type, vpiHandle ref1,
                                     vpiHandle ref2) {
  return vpi_handle_multi(type, ref1, ref2);
}
vpiHandle vpi_put_value_1364v1995(vpiHandle obj, s_vpi_value* value,
                                  s_vpi_time* time, PLI_INT32 flags) {
  return vpi_put_value(obj, value, time, flags);
}
vpiHandle vpi_register_cb_1364v1995(s_cb_data* data) {
  return vpi_register_cb(data);
}
vpiHandle vpi_scan_1364v1995(vpiHandle iterator) { return vpi_scan(iterator); }
PLI_INT32 vpi_control_1364v1995(PLI_INT32 operation, ...) {
  va_list args;
  va_start(args, operation);
  PLI_INT32 result = VpiControlWithArgs(operation, args);
  va_end(args);
  return result;
}
vpiHandle vpi_iterate_1364v1995(PLI_INT32 type, vpiHandle ref) {
  // §36.12.2.2: an application using Mechanism 1 is governed by the mode
  // compiled into it, whatever default the run was given.
  return delta::VpiIterateInCompatibilityMode(
      type, ref,
      delta::GetGlobalVpiContext().EffectiveCompatibilityMode(
          true, vpiMode1364v1995));
}

// IEEE Std 1364-2001.
PLI_INT32 vpi_compare_objects_1364v2001(vpiHandle obj1, vpiHandle obj2) {
  return vpi_compare_objects(obj1, obj2);
}
PLI_INT32 vpi_get_1364v2001(PLI_INT32 property, vpiHandle obj) {
  return vpi_get(property, obj);
}
PLI_BYTE8* vpi_get_str_1364v2001(PLI_INT32 property, vpiHandle obj) {
  return vpi_get_str(property, obj);
}
void vpi_get_value_1364v2001(vpiHandle obj, s_vpi_value* value) {
  vpi_get_value(obj, value);
}
vpiHandle vpi_handle_1364v2001(PLI_INT32 type, vpiHandle ref) {
  return vpi_handle(type, ref);
}
vpiHandle vpi_handle_by_index_1364v2001(vpiHandle parent, PLI_INT32 index) {
  return vpi_handle_by_index(parent, index);
}
vpiHandle vpi_handle_by_multi_index_1364v2001(vpiHandle parent,
                                              PLI_INT32 num_index,
                                              PLI_INT32* index_array) {
  return vpi_handle_by_multi_index(parent, num_index, index_array);
}
vpiHandle vpi_handle_by_name_1364v2001(const char* name, vpiHandle scope) {
  return vpi_handle_by_name(name, scope);
}
vpiHandle vpi_handle_multi_1364v2001(PLI_INT32 type, vpiHandle ref1,
                                     vpiHandle ref2) {
  return vpi_handle_multi(type, ref1, ref2);
}
vpiHandle vpi_put_value_1364v2001(vpiHandle obj, s_vpi_value* value,
                                  s_vpi_time* time, PLI_INT32 flags) {
  return vpi_put_value(obj, value, time, flags);
}
vpiHandle vpi_register_cb_1364v2001(s_cb_data* data) {
  return vpi_register_cb(data);
}
vpiHandle vpi_scan_1364v2001(vpiHandle iterator) { return vpi_scan(iterator); }
PLI_INT32 vpi_control_1364v2001(PLI_INT32 operation, ...) {
  va_list args;
  va_start(args, operation);
  PLI_INT32 result = VpiControlWithArgs(operation, args);
  va_end(args);
  return result;
}
vpiHandle vpi_iterate_1364v2001(PLI_INT32 type, vpiHandle ref) {
  // §36.12.2.2: an application using Mechanism 1 is governed by the mode
  // compiled into it, whatever default the run was given.
  return delta::VpiIterateInCompatibilityMode(
      type, ref,
      delta::GetGlobalVpiContext().EffectiveCompatibilityMode(
          true, vpiMode1364v2001));
}

// IEEE Std 1364-2005.
PLI_INT32 vpi_compare_objects_1364v2005(vpiHandle obj1, vpiHandle obj2) {
  return vpi_compare_objects(obj1, obj2);
}
PLI_INT32 vpi_get_1364v2005(PLI_INT32 property, vpiHandle obj) {
  return vpi_get(property, obj);
}
PLI_BYTE8* vpi_get_str_1364v2005(PLI_INT32 property, vpiHandle obj) {
  return vpi_get_str(property, obj);
}
void vpi_get_value_1364v2005(vpiHandle obj, s_vpi_value* value) {
  vpi_get_value(obj, value);
}
vpiHandle vpi_handle_1364v2005(PLI_INT32 type, vpiHandle ref) {
  return vpi_handle(type, ref);
}
vpiHandle vpi_handle_by_index_1364v2005(vpiHandle parent, PLI_INT32 index) {
  return vpi_handle_by_index(parent, index);
}
vpiHandle vpi_handle_by_multi_index_1364v2005(vpiHandle parent,
                                              PLI_INT32 num_index,
                                              PLI_INT32* index_array) {
  return vpi_handle_by_multi_index(parent, num_index, index_array);
}
vpiHandle vpi_handle_by_name_1364v2005(const char* name, vpiHandle scope) {
  return vpi_handle_by_name(name, scope);
}
vpiHandle vpi_handle_multi_1364v2005(PLI_INT32 type, vpiHandle ref1,
                                     vpiHandle ref2) {
  return vpi_handle_multi(type, ref1, ref2);
}
vpiHandle vpi_put_value_1364v2005(vpiHandle obj, s_vpi_value* value,
                                  s_vpi_time* time, PLI_INT32 flags) {
  return vpi_put_value(obj, value, time, flags);
}
vpiHandle vpi_register_cb_1364v2005(s_cb_data* data) {
  return vpi_register_cb(data);
}
vpiHandle vpi_scan_1364v2005(vpiHandle iterator) { return vpi_scan(iterator); }
PLI_INT32 vpi_control_1364v2005(PLI_INT32 operation, ...) {
  va_list args;
  va_start(args, operation);
  PLI_INT32 result = VpiControlWithArgs(operation, args);
  va_end(args);
  return result;
}
vpiHandle vpi_iterate_1364v2005(PLI_INT32 type, vpiHandle ref) {
  // §36.12.2.2: an application using Mechanism 1 is governed by the mode
  // compiled into it, whatever default the run was given.
  return delta::VpiIterateInCompatibilityMode(
      type, ref,
      delta::GetGlobalVpiContext().EffectiveCompatibilityMode(
          true, vpiMode1364v2005));
}

// IEEE Std 1800-2005.
PLI_INT32 vpi_compare_objects_1800v2005(vpiHandle obj1, vpiHandle obj2) {
  return vpi_compare_objects(obj1, obj2);
}
PLI_INT32 vpi_get_1800v2005(PLI_INT32 property, vpiHandle obj) {
  return vpi_get(property, obj);
}
PLI_BYTE8* vpi_get_str_1800v2005(PLI_INT32 property, vpiHandle obj) {
  return vpi_get_str(property, obj);
}
void vpi_get_value_1800v2005(vpiHandle obj, s_vpi_value* value) {
  vpi_get_value(obj, value);
}
vpiHandle vpi_handle_1800v2005(PLI_INT32 type, vpiHandle ref) {
  return vpi_handle(type, ref);
}
vpiHandle vpi_handle_by_index_1800v2005(vpiHandle parent, PLI_INT32 index) {
  return vpi_handle_by_index(parent, index);
}
vpiHandle vpi_handle_by_multi_index_1800v2005(vpiHandle parent,
                                              PLI_INT32 num_index,
                                              PLI_INT32* index_array) {
  return vpi_handle_by_multi_index(parent, num_index, index_array);
}
vpiHandle vpi_handle_by_name_1800v2005(const char* name, vpiHandle scope) {
  return vpi_handle_by_name(name, scope);
}
vpiHandle vpi_handle_multi_1800v2005(PLI_INT32 type, vpiHandle ref1,
                                     vpiHandle ref2) {
  return vpi_handle_multi(type, ref1, ref2);
}
vpiHandle vpi_put_value_1800v2005(vpiHandle obj, s_vpi_value* value,
                                  s_vpi_time* time, PLI_INT32 flags) {
  return vpi_put_value(obj, value, time, flags);
}
vpiHandle vpi_register_cb_1800v2005(s_cb_data* data) {
  return vpi_register_cb(data);
}
vpiHandle vpi_scan_1800v2005(vpiHandle iterator) { return vpi_scan(iterator); }
PLI_INT32 vpi_control_1800v2005(PLI_INT32 operation, ...) {
  va_list args;
  va_start(args, operation);
  PLI_INT32 result = VpiControlWithArgs(operation, args);
  va_end(args);
  return result;
}
vpiHandle vpi_iterate_1800v2005(PLI_INT32 type, vpiHandle ref) {
  return delta::VpiIterateInCompatibilityMode(
      type, ref,
      delta::GetGlobalVpiContext().EffectiveCompatibilityMode(
          true, vpiMode1800v2005));
}

// IEEE Std 1800-2009.
PLI_INT32 vpi_compare_objects_1800v2009(vpiHandle obj1, vpiHandle obj2) {
  return vpi_compare_objects(obj1, obj2);
}
PLI_INT32 vpi_get_1800v2009(PLI_INT32 property, vpiHandle obj) {
  return vpi_get(property, obj);
}
PLI_BYTE8* vpi_get_str_1800v2009(PLI_INT32 property, vpiHandle obj) {
  return vpi_get_str(property, obj);
}
void vpi_get_value_1800v2009(vpiHandle obj, s_vpi_value* value) {
  vpi_get_value(obj, value);
}
vpiHandle vpi_handle_1800v2009(PLI_INT32 type, vpiHandle ref) {
  return vpi_handle(type, ref);
}
vpiHandle vpi_handle_by_index_1800v2009(vpiHandle parent, PLI_INT32 index) {
  return vpi_handle_by_index(parent, index);
}
vpiHandle vpi_handle_by_multi_index_1800v2009(vpiHandle parent,
                                              PLI_INT32 num_index,
                                              PLI_INT32* index_array) {
  return vpi_handle_by_multi_index(parent, num_index, index_array);
}
vpiHandle vpi_handle_by_name_1800v2009(const char* name, vpiHandle scope) {
  return vpi_handle_by_name(name, scope);
}
vpiHandle vpi_handle_multi_1800v2009(PLI_INT32 type, vpiHandle ref1,
                                     vpiHandle ref2) {
  return vpi_handle_multi(type, ref1, ref2);
}
vpiHandle vpi_put_value_1800v2009(vpiHandle obj, s_vpi_value* value,
                                  s_vpi_time* time, PLI_INT32 flags) {
  return vpi_put_value(obj, value, time, flags);
}
vpiHandle vpi_register_cb_1800v2009(s_cb_data* data) {
  return vpi_register_cb(data);
}
vpiHandle vpi_scan_1800v2009(vpiHandle iterator) { return vpi_scan(iterator); }
PLI_INT32 vpi_control_1800v2009(PLI_INT32 operation, ...) {
  va_list args;
  va_start(args, operation);
  PLI_INT32 result = VpiControlWithArgs(operation, args);
  va_end(args);
  return result;
}
vpiHandle vpi_iterate_1800v2009(PLI_INT32 type, vpiHandle ref) {
  return delta::VpiIterateInCompatibilityMode(
      type, ref,
      delta::GetGlobalVpiContext().EffectiveCompatibilityMode(
          true, vpiMode1800v2009));
}

// IEEE Std 1800-2012.
PLI_INT32 vpi_compare_objects_1800v2012(vpiHandle obj1, vpiHandle obj2) {
  return vpi_compare_objects(obj1, obj2);
}
PLI_INT32 vpi_get_1800v2012(PLI_INT32 property, vpiHandle obj) {
  return vpi_get(property, obj);
}
PLI_BYTE8* vpi_get_str_1800v2012(PLI_INT32 property, vpiHandle obj) {
  return vpi_get_str(property, obj);
}
void vpi_get_value_1800v2012(vpiHandle obj, s_vpi_value* value) {
  vpi_get_value(obj, value);
}
vpiHandle vpi_handle_1800v2012(PLI_INT32 type, vpiHandle ref) {
  return vpi_handle(type, ref);
}
vpiHandle vpi_handle_by_index_1800v2012(vpiHandle parent, PLI_INT32 index) {
  return vpi_handle_by_index(parent, index);
}
vpiHandle vpi_handle_by_multi_index_1800v2012(vpiHandle parent,
                                              PLI_INT32 num_index,
                                              PLI_INT32* index_array) {
  return vpi_handle_by_multi_index(parent, num_index, index_array);
}
vpiHandle vpi_handle_by_name_1800v2012(const char* name, vpiHandle scope) {
  return vpi_handle_by_name(name, scope);
}
vpiHandle vpi_handle_multi_1800v2012(PLI_INT32 type, vpiHandle ref1,
                                     vpiHandle ref2) {
  return vpi_handle_multi(type, ref1, ref2);
}
vpiHandle vpi_put_value_1800v2012(vpiHandle obj, s_vpi_value* value,
                                  s_vpi_time* time, PLI_INT32 flags) {
  return vpi_put_value(obj, value, time, flags);
}
vpiHandle vpi_register_cb_1800v2012(s_cb_data* data) {
  return vpi_register_cb(data);
}
vpiHandle vpi_scan_1800v2012(vpiHandle iterator) { return vpi_scan(iterator); }
PLI_INT32 vpi_control_1800v2012(PLI_INT32 operation, ...) {
  va_list args;
  va_start(args, operation);
  PLI_INT32 result = VpiControlWithArgs(operation, args);
  va_end(args);
  return result;
}
vpiHandle vpi_iterate_1800v2012(PLI_INT32 type, vpiHandle ref) {
  return delta::VpiIterateInCompatibilityMode(
      type, ref,
      delta::GetGlobalVpiContext().EffectiveCompatibilityMode(true, 0));
}
