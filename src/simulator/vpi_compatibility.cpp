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

// §36.12.1 Table 36-10 rows 1 and 2 with Annex C.4.3 items 1 and 2: vpiMemory
// and vpiMemoryWord are object types "under certain backwards compatibility
// modes", present in IEEE Std 1364-1995 and, deprecated, in IEEE Std 1364-2001
// (Y and D), and "no longer present" from IEEE Std 1364-2005 on, where a memory
// is a vpiRegArray and its word a vpiReg as in this standard.
bool VpiModeHasMemoryObjects(int mode) {
  return mode == vpiMode1364v1995 || mode == vpiMode1364v2001;
}

// Rows 3 and 4 with C.4.3 item 3: vpiIntegerVar and vpiTimeVar "can be arrays"
// in every IEEE 1364 standard and vpiRealVar in IEEE Std 1364-2001 and
// 1364-2005, "instead of simple variables", so an unpacked array of one of
// those kinds is an object of that kind under such a mode, told from the
// simple variable by the vpiArray property. The kind such a mode reads
// `array` as, or 0 for an array it reads as an array object.
int Vpi1364ArrayAsVariableKind(delta::VpiHandle array, int mode) {
  for (const auto* word : array->children) {
    if (word->type == vpiIntegerVar || word->type == vpiTimeVar) {
      return word->type;
    }
    if (word->type == vpiRealVar && mode != vpiMode1364v1995) {
      return word->type;
    }
  }
  return 0;
}

// The vpiType an IEEE 1364 mode reports for `obj`, or 0 where it reports the
// kind this standard does. Row 1 has "unpacked unidimensional reg arrays"
// characterized as vpiMemory objects; an array of more dimensions is the
// vpiRegArray IEEE Std 1364-2001 introduced for it.
int Vpi1364Type(delta::VpiHandle obj, int mode) {
  if (delta::VpiIsArrayVarType(obj->type)) {
    if (obj->array_dim_indices.size() > 1) return 0;
    if (delta::VpiArrayVarIsMemory(obj)) {
      return VpiModeHasMemoryObjects(mode) ? vpiMemory : 0;
    }
    return Vpi1364ArrayAsVariableKind(obj, mode);
  }
  if (obj->type == vpiReg && VpiModeHasMemoryObjects(mode) &&
      delta::VpiArrayVarIsMemory(obj->parent)) {
    return vpiMemoryWord;
  }
  return 0;
}

// Row 3 and C.4.3 item 3: the vpiArray property "returned TRUE when they were
// arrays" for the integer, time and real variables an IEEE 1364 mode reads an
// array as, and "indicated when vpiReg types represented elements of
// vpiRegArrays"; FALSE for every other object under such a mode.
int Vpi1364ArrayProperty(delta::VpiHandle obj, int mode) {
  if (delta::VpiIsArrayVarType(obj->type)) {
    return Vpi1364ArrayAsVariableKind(obj, mode) != 0 ? 1 : 0;
  }
  return obj->type == vpiReg && delta::VpiVariableIsArrayMember(obj) ? 1 : 0;
}

}  // namespace

namespace delta {

const char* VpiCompatibilityUnsupportedConstruct(
    int mode, const std::vector<VpiObject*>& objects) {
  // §36.12.3 leaves "the extent of checking for consistency between constructs
  // and mode ... to the discretion of the VPI implementation", and this is the
  // extent of it. Annex K reserves the object-type values 1 through 299 for
  // vpi_user.h and Annex M reserves 600 through 999 for the SystemVerilog
  // extensions, so a kind numbered in Annex M's range is a construct the IEEE
  // 1364 standards have no notion of. An application running under one of their
  // modes that reaches such an object is applied to a design §36.12.2 says the
  // mechanism does not cover, and it is told so.
  if (!VpiModeIs1364(mode)) return nullptr;
  for (const auto* object : objects) {
    if (object->type >= 600 && object->type <= 999) {
      return "vpi_iterate(): the design contains a construct the selected VPI "
             "compatibility mode has no notion of";
    }
  }
  return nullptr;
}

int VpiGetInCompatibilityMode(int property, VpiHandle obj, int mode) {
  // The property as the current routine answers it, with an error it recorded
  // kept; under an IEEE 1364 mode the object type and vpiArray property are
  // then the ones Table 36-10 rows 1 through 4 give that version, and every
  // other property is the current one.
  int value = delta::GetGlobalVpiContext().Get(property, obj);
  if (value == vpiUndefined || obj == nullptr || !VpiModeIs1364(mode)) {
    return value;
  }
  if (property == vpiType) {
    int older = Vpi1364Type(obj, mode);
    return older != 0 ? older : value;
  }
  if (property == vpiArray) return Vpi1364ArrayProperty(obj, mode);
  return value;
}

vpiHandle VpiIterateInCompatibilityMode(int type, VpiHandle ref, int mode) {
  // The iterator the current routine builds, with the objects an application
  // of `mode` does not expect dropped. An iteration left with nothing is the
  // NULL §38.23 gives one that reaches no object, so the emptied iterator is
  // released rather than handed back.
  vpiHandle iterator = delta::GetGlobalVpiContext().Iterate(type, ref, mode);
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
  return delta::VpiGetInCompatibilityMode(
      property, obj,
      delta::GetGlobalVpiContext().EffectiveCompatibilityMode(
          true, vpiMode1364v1995));
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
  return delta::VpiGetInCompatibilityMode(
      property, obj,
      delta::GetGlobalVpiContext().EffectiveCompatibilityMode(
          true, vpiMode1364v2001));
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
  return delta::VpiGetInCompatibilityMode(
      property, obj,
      delta::GetGlobalVpiContext().EffectiveCompatibilityMode(
          true, vpiMode1364v2005));
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
