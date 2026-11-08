#include <cstdarg>
#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_routine_error_scope.h"
#include "simulator/vpi_user.h"

PLI_INT32 VpiControlWithArgs(PLI_INT32 operation, va_list args);

namespace {

bool Vpi1364VariablesKeeps(int obj_type) {
  return obj_type != vpiReg && obj_type != vpiRegArray;
}

bool Vpi1364IterationKeeps(int type, delta::VpiHandle ref,
                           delta::VpiHandle object) {
  if (type == vpiVariables) return Vpi1364VariablesKeeps(object->type);
  if (type == vpiReg && ref != nullptr && delta::VpiIsArrayVarType(ref->type)) {
    return object->type == vpiReg;
  }
  if (type == vpiRegArray) return delta::VpiArrayVarIsMemory(object);
  return true;
}

bool VpiModeIs1364(int mode) {
  return mode == vpiMode1364v1995 || mode == vpiMode1364v2001 ||
         mode == vpiMode1364v2005;
}

bool VpiModeHasMemoryObjects(int mode) {
  return mode == vpiMode1364v1995 || mode == vpiMode1364v2001;
}

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

VpiHandle VpiIterateInCompatibilityMode(int type, VpiHandle ref, int mode) {
  VpiContext& vpi = delta::GetGlobalVpiContext();
  if (vpi.RoutineIsUnavailableNow(VpiRoutine::kIterate)) return nullptr;
  VpiHandle iterator = vpi.Iterate(type, ref, mode);
  if (iterator == nullptr || !VpiModeIs1364(mode)) return iterator;
  std::vector<delta::VpiObject*> kept;
  for (auto* object : iterator->children) {
    if (Vpi1364IterationKeeps(type, ref, object)) kept.push_back(object);
  }
  iterator->children = kept;
  if (!iterator->children.empty()) return iterator;
  vpi_release_handle(delta::VpiHandleOf(iterator));
  return nullptr;
}

}  // namespace delta

extern "C" {

PLI_INT32 vpi_compare_objects_1364v1995(vpiHandle obj1, vpiHandle obj2) {
  return vpi_compare_objects(obj1, obj2);
}
PLI_INT32 vpi_get_1364v1995(PLI_INT32 property, vpiHandle obj) {
  delta::VpiRoutineErrorScope error_scope;
  return delta::VpiGetInCompatibilityMode(
      property, delta::VpiObjectOf(obj),
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
vpiHandle vpi_handle_by_name_1364v1995(PLI_BYTE8* name, vpiHandle scope) {
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
  delta::VpiRoutineErrorScope error_scope;
  va_list args;
  va_start(args, operation);
  PLI_INT32 result = VpiControlWithArgs(operation, args);
  va_end(args);
  return result;
}
vpiHandle vpi_iterate_1364v1995(PLI_INT32 type, vpiHandle ref) {
  delta::VpiRoutineErrorScope error_scope;
  return delta::VpiHandleOf(delta::VpiIterateInCompatibilityMode(
      type, delta::VpiObjectOf(ref),
      delta::GetGlobalVpiContext().EffectiveCompatibilityMode(
          true, vpiMode1364v1995)));
}

PLI_INT32 vpi_compare_objects_1364v2001(vpiHandle obj1, vpiHandle obj2) {
  return vpi_compare_objects(obj1, obj2);
}
PLI_INT32 vpi_get_1364v2001(PLI_INT32 property, vpiHandle obj) {
  delta::VpiRoutineErrorScope error_scope;
  return delta::VpiGetInCompatibilityMode(
      property, delta::VpiObjectOf(obj),
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
vpiHandle vpi_handle_by_name_1364v2001(PLI_BYTE8* name, vpiHandle scope) {
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
  delta::VpiRoutineErrorScope error_scope;
  va_list args;
  va_start(args, operation);
  PLI_INT32 result = VpiControlWithArgs(operation, args);
  va_end(args);
  return result;
}
vpiHandle vpi_iterate_1364v2001(PLI_INT32 type, vpiHandle ref) {
  delta::VpiRoutineErrorScope error_scope;
  return delta::VpiHandleOf(delta::VpiIterateInCompatibilityMode(
      type, delta::VpiObjectOf(ref),
      delta::GetGlobalVpiContext().EffectiveCompatibilityMode(
          true, vpiMode1364v2001)));
}

PLI_INT32 vpi_compare_objects_1364v2005(vpiHandle obj1, vpiHandle obj2) {
  return vpi_compare_objects(obj1, obj2);
}
PLI_INT32 vpi_get_1364v2005(PLI_INT32 property, vpiHandle obj) {
  delta::VpiRoutineErrorScope error_scope;
  return delta::VpiGetInCompatibilityMode(
      property, delta::VpiObjectOf(obj),
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
vpiHandle vpi_handle_by_name_1364v2005(PLI_BYTE8* name, vpiHandle scope) {
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
  delta::VpiRoutineErrorScope error_scope;
  va_list args;
  va_start(args, operation);
  PLI_INT32 result = VpiControlWithArgs(operation, args);
  va_end(args);
  return result;
}
vpiHandle vpi_iterate_1364v2005(PLI_INT32 type, vpiHandle ref) {
  delta::VpiRoutineErrorScope error_scope;
  return delta::VpiHandleOf(delta::VpiIterateInCompatibilityMode(
      type, delta::VpiObjectOf(ref),
      delta::GetGlobalVpiContext().EffectiveCompatibilityMode(
          true, vpiMode1364v2005)));
}

PLI_INT32 vpi_compare_objects_1800v2005(vpiHandle obj1, vpiHandle obj2) {
  return vpi_compare_objects(obj1, obj2);
}
PLI_INT32 vpi_get_1800v2005(PLI_INT32 property, vpiHandle obj) {
  delta::VpiRoutineErrorScope error_scope;
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
vpiHandle vpi_handle_by_name_1800v2005(PLI_BYTE8* name, vpiHandle scope) {
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
  delta::VpiRoutineErrorScope error_scope;
  va_list args;
  va_start(args, operation);
  PLI_INT32 result = VpiControlWithArgs(operation, args);
  va_end(args);
  return result;
}
vpiHandle vpi_iterate_1800v2005(PLI_INT32 type, vpiHandle ref) {
  delta::VpiRoutineErrorScope error_scope;
  return delta::VpiHandleOf(delta::VpiIterateInCompatibilityMode(
      type, delta::VpiObjectOf(ref),
      delta::GetGlobalVpiContext().EffectiveCompatibilityMode(
          true, vpiMode1800v2005)));
}

PLI_INT32 vpi_compare_objects_1800v2009(vpiHandle obj1, vpiHandle obj2) {
  return vpi_compare_objects(obj1, obj2);
}
PLI_INT32 vpi_get_1800v2009(PLI_INT32 property, vpiHandle obj) {
  delta::VpiRoutineErrorScope error_scope;
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
vpiHandle vpi_handle_by_name_1800v2009(PLI_BYTE8* name, vpiHandle scope) {
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
  delta::VpiRoutineErrorScope error_scope;
  va_list args;
  va_start(args, operation);
  PLI_INT32 result = VpiControlWithArgs(operation, args);
  va_end(args);
  return result;
}
vpiHandle vpi_iterate_1800v2009(PLI_INT32 type, vpiHandle ref) {
  delta::VpiRoutineErrorScope error_scope;
  return delta::VpiHandleOf(delta::VpiIterateInCompatibilityMode(
      type, delta::VpiObjectOf(ref),
      delta::GetGlobalVpiContext().EffectiveCompatibilityMode(
          true, vpiMode1800v2009)));
}

PLI_INT32 vpi_compare_objects_1800v2012(vpiHandle obj1, vpiHandle obj2) {
  return vpi_compare_objects(obj1, obj2);
}
PLI_INT32 vpi_get_1800v2012(PLI_INT32 property, vpiHandle obj) {
  delta::VpiRoutineErrorScope error_scope;
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
vpiHandle vpi_handle_by_name_1800v2012(PLI_BYTE8* name, vpiHandle scope) {
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
  delta::VpiRoutineErrorScope error_scope;
  va_list args;
  va_start(args, operation);
  PLI_INT32 result = VpiControlWithArgs(operation, args);
  va_end(args);
  return result;
}
vpiHandle vpi_iterate_1800v2012(PLI_INT32 type, vpiHandle ref) {
  delta::VpiRoutineErrorScope error_scope;
  return delta::VpiHandleOf(delta::VpiIterateInCompatibilityMode(
      type, delta::VpiObjectOf(ref),
      delta::GetGlobalVpiContext().EffectiveCompatibilityMode(true, 0)));
}
}
