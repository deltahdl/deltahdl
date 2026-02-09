#include "simulation/vpi.h"

#include <cstddef>
#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

namespace delta {

VpiContext::~VpiContext() {
  for (auto* obj : all_objects_) {
    delete obj;
  }
}

void VpiContext::Attach(SimContext& sim_ctx) {
  for (auto& [name, var] : sim_ctx.GetVariables()) {
    auto* obj = new VpiObject();
    obj->type = kVpiReg;
    obj->name = name;
    obj->var = var;
    object_map_[name] = obj;
    all_objects_.push_back(obj);
  }
}

VpiHandle VpiContext::RegisterSystf(VpiSystfData* data) {
  if (!data) return nullptr;
  systfs_.push_back(*data);
  return nullptr;
}

VpiHandle VpiContext::HandleByName(const char* name, VpiHandle /*scope*/) {
  if (!name) return nullptr;
  auto it = object_map_.find(std::string_view(name));
  if (it != object_map_.end()) return it->second;
  return nullptr;
}

VpiHandle VpiContext::Iterate(int type, VpiHandle /*ref*/) {
  auto* iter = new VpiObject();
  iter->type = type;
  iter->scan_index = 0;
  for (auto* obj : all_objects_) {
    if (obj->type == type) iter->children.push_back(obj);
  }
  if (iter->children.empty()) {
    delete iter;
    return nullptr;
  }
  return iter;
}

VpiHandle VpiContext::Scan(VpiHandle iterator) {
  if (!iterator) return nullptr;
  if (iterator->scan_index >= iterator->children.size()) {
    delete iterator;
    return nullptr;
  }
  return iterator->children[iterator->scan_index++];
}

void VpiContext::GetValue(VpiHandle obj, VpiValue* value) {
  if (!obj || !value || !obj->var) return;
  if (value->format == kVpiIntVal) {
    value->value.integer = static_cast<int>(obj->var->value.ToUint64());
  }
}

void VpiContext::PutValue(VpiHandle obj, VpiValue* value, VpiTime* /*time*/,
                          int /*flags*/) {
  if (!obj || !value || !obj->var) return;
  if (value->format == kVpiIntVal) {
    uint64_t new_val = static_cast<uint64_t>(value->value.integer);
    obj->var->value.words[0].aval = new_val;
    obj->var->value.words[0].bval = 0;
  }
}

VpiHandle VpiContext::RegisterCb(VpiCbData* data) {
  if (!data) return nullptr;
  callbacks_.push_back(*data);
  return nullptr;
}

void VpiContext::RegisterCbValueChange(const VpiCbData& data) {
  if (!data.obj || !data.obj->var) return;
  void* user_data = data.user_data;
  data.obj->var->AddWatcher([user_data]() {
    if (user_data) *static_cast<bool*>(user_data) = true;
  });
}

int VpiContext::Get(int property, VpiHandle obj) {
  if (!obj) return 0;
  if (property == kVpiType) return obj->type;
  return 0;
}

const char* VpiContext::GetStr(int property, VpiHandle obj) {
  if (!obj) return nullptr;
  if (property == kVpiName) return obj->name.data();
  return nullptr;
}

int VpiContext::FreeObject(VpiHandle /*obj*/) { return 0; }

// --- Global context singleton ---

static VpiContext* g_vpi_context = nullptr;
static VpiContext g_default_context;

VpiContext& GetGlobalVpiContext() {
  if (g_vpi_context) return *g_vpi_context;
  return g_default_context;
}

void SetGlobalVpiContext(VpiContext* ctx) { g_vpi_context = ctx; }

}  // namespace delta

// --- C API implementations ---

vpiHandle vpi_register_systf(s_vpi_systf_data* data) {
  return delta::GetGlobalVpiContext().RegisterSystf(data);
}

vpiHandle vpi_handle_by_name(const char* name, vpiHandle scope) {
  return delta::GetGlobalVpiContext().HandleByName(name, scope);
}

vpiHandle vpi_iterate(int type, vpiHandle ref) {
  return delta::GetGlobalVpiContext().Iterate(type, ref);
}

vpiHandle vpi_scan(vpiHandle iterator) {
  return delta::GetGlobalVpiContext().Scan(iterator);
}

void vpi_get_value(vpiHandle obj, s_vpi_value* value) {
  delta::GetGlobalVpiContext().GetValue(obj, value);
}

void vpi_put_value(vpiHandle obj, s_vpi_value* value, s_vpi_time* time,
                   int flags) {
  delta::GetGlobalVpiContext().PutValue(obj, value, time, flags);
}

vpiHandle vpi_register_cb(s_cb_data* data) {
  return delta::GetGlobalVpiContext().RegisterCb(data);
}

int vpi_get(int property, vpiHandle obj) {
  return delta::GetGlobalVpiContext().Get(property, obj);
}

const char* vpi_get_str(int property, vpiHandle obj) {
  return delta::GetGlobalVpiContext().GetStr(property, obj);
}

int vpi_free_object(vpiHandle obj) {
  return delta::GetGlobalVpiContext().FreeObject(obj);
}
