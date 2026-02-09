#include "simulation/vpi.h"

#include <cstddef>

namespace delta {

VpiHandle VpiContext::RegisterSystf(VpiSystfData* data) {
  if (!data) return nullptr;
  systfs_.push_back(*data);
  // Stub: return nullptr since we don't yet create real VPI objects.
  return nullptr;
}

VpiHandle VpiContext::HandleByName(const char* /*name*/, VpiHandle /*scope*/) {
  // Stub: no design objects resolved yet.
  return nullptr;
}

VpiHandle VpiContext::Iterate(int /*type*/, VpiHandle /*ref*/) {
  // Stub: no iteration support yet.
  return nullptr;
}

VpiHandle VpiContext::Scan(VpiHandle /*iterator*/) {
  // Stub: no iterator objects yet.
  return nullptr;
}

void VpiContext::GetValue(VpiHandle obj, VpiValue* value) {
  if (!obj || !value) return;
  // Stub: zero-fill the value.
  value->value = {};
}

void VpiContext::PutValue(VpiHandle obj, VpiValue* /*value*/, VpiTime* /*time*/,
                          int /*flags*/) {
  if (!obj) return;
  // Stub: no-op.
}

VpiHandle VpiContext::RegisterCb(VpiCbData* data) {
  if (!data) return nullptr;
  callbacks_.push_back(*data);
  return nullptr;
}

int VpiContext::Get(int /*property*/, VpiHandle /*obj*/) {
  // Stub: return 0.
  return 0;
}

const char* VpiContext::GetStr(int /*property*/, VpiHandle /*obj*/) {
  // Stub: return nullptr.
  return nullptr;
}

int VpiContext::FreeObject(VpiHandle /*obj*/) {
  // Stub: nothing to free yet.
  return 0;
}

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
