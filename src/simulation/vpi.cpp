#include "simulation/vpi.h"

#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string>
#include <string_view>

#include "common/types.h"
#include "simulation/net.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

namespace delta {

VpiContext::~VpiContext() {
  for (auto* obj : all_objects_) {
    delete obj;
  }
}

VpiHandle VpiContext::AllocObject() {
  auto* obj = new VpiObject();
  all_objects_.push_back(obj);
  return obj;
}

void VpiContext::Attach(SimContext& sim_ctx) {
  for (auto& [name, var] : sim_ctx.GetVariables()) {
    auto* obj = AllocObject();
    obj->type = kVpiReg;
    obj->name = name;
    obj->var = var;
    obj->size = static_cast<int>(var->value.width);
    object_map_[name] = obj;
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

VpiHandle VpiContext::HandleByIndex(int index, VpiHandle parent) {
  if (!parent) return nullptr;
  for (auto* child : parent->children) {
    if (child->index == index) return child;
  }
  return nullptr;
}

VpiHandle VpiContext::Handle(int type, VpiHandle ref) {
  if (!ref) return nullptr;
  // Return parent if it matches the requested type.
  if (ref->parent && ref->parent->type == type) return ref->parent;
  // Search children for matching type.
  for (auto* child : ref->children) {
    if (child->type == type) return child;
  }
  return nullptr;
}

VpiHandle VpiContext::Iterate(int type, VpiHandle ref) {
  auto* iter = new VpiObject();
  iter->type = type;
  iter->scan_index = 0;

  if (ref) {
    for (auto* child : ref->children) {
      if (child->type == type) iter->children.push_back(child);
    }
  } else {
    for (auto* obj : all_objects_) {
      if (obj->type == type) iter->children.push_back(obj);
    }
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

// --- Value format helpers ---

static void GetValueBinStr(VpiHandle obj, VpiValue* value,
                           std::vector<std::string>& pool) {
  uint64_t aval = obj->var->value.words[0].aval;
  uint64_t bval = obj->var->value.words[0].bval;
  int width = static_cast<int>(obj->var->value.width);
  std::string result;
  result.reserve(width);
  for (int i = width - 1; i >= 0; --i) {
    bool a_bit = (aval >> i) & 1;
    bool b_bit = (bval >> i) & 1;
    if (!b_bit) {
      result += (a_bit ? '1' : '0');
    } else {
      result += (a_bit ? 'z' : 'x');
    }
  }
  pool.push_back(std::move(result));
  value->value.str = pool.back().c_str();
}

static char HexDigitFromBits(uint8_t nibble) {
  if (nibble < 10) return static_cast<char>('0' + nibble);
  return static_cast<char>('a' + nibble - 10);
}

static void GetValueHexStr(VpiHandle obj, VpiValue* value,
                           std::vector<std::string>& pool) {
  uint64_t aval = obj->var->value.words[0].aval;
  uint64_t bval = obj->var->value.words[0].bval;
  int width = static_cast<int>(obj->var->value.width);
  int hex_digits = (width + 3) / 4;
  std::string result;
  result.reserve(hex_digits);
  for (int i = hex_digits - 1; i >= 0; --i) {
    uint8_t a_nibble = (aval >> (i * 4)) & 0xF;
    uint8_t b_nibble = (bval >> (i * 4)) & 0xF;
    if (b_nibble != 0) {
      result += (b_nibble == 0xF && a_nibble == 0xF) ? 'z' : 'x';
    } else {
      result += HexDigitFromBits(a_nibble);
    }
  }
  pool.push_back(std::move(result));
  value->value.str = pool.back().c_str();
}

static void GetValueOctStr(VpiHandle obj, VpiValue* value,
                           std::vector<std::string>& pool) {
  uint64_t aval = obj->var->value.words[0].aval;
  int width = static_cast<int>(obj->var->value.width);
  int oct_digits = (width + 2) / 3;
  std::string result;
  result.reserve(oct_digits);
  for (int i = oct_digits - 1; i >= 0; --i) {
    uint8_t bits = (aval >> (i * 3)) & 0x7;
    result += static_cast<char>('0' + bits);
  }
  pool.push_back(std::move(result));
  value->value.str = pool.back().c_str();
}

static int ScalarFromBits(uint64_t aval, uint64_t bval) {
  if (!bval) return aval ? kVpi1 : kVpi0;
  return aval ? kVpiZ : kVpiX;
}

static void GetValueStringVal(VpiHandle obj, VpiValue* value,
                              std::vector<std::string>& pool) {
  uint64_t val = obj->var->value.ToUint64();
  std::string s;
  for (int i = 56; i >= 0; i -= 8) {
    auto ch = static_cast<char>((val >> i) & 0xFF);
    if (ch != 0) s += ch;
  }
  pool.push_back(std::move(s));
  value->value.str = pool.back().c_str();
}

void VpiContext::GetValue(VpiHandle obj, VpiValue* value) {
  if (!obj || !value || !obj->var) return;
  switch (value->format) {
    case kVpiIntVal:
      value->value.integer = static_cast<int>(obj->var->value.ToUint64());
      break;
    case kVpiRealVal:
      value->value.real = static_cast<double>(obj->var->value.ToUint64());
      break;
    case kVpiScalarVal:
      value->value.scalar = ScalarFromBits(obj->var->value.words[0].aval & 1,
                                           obj->var->value.words[0].bval & 1);
      break;
    case kVpiBinStrVal:
      GetValueBinStr(obj, value, str_pool_);
      break;
    case kVpiHexStrVal:
      GetValueHexStr(obj, value, str_pool_);
      break;
    case kVpiOctStrVal:
      GetValueOctStr(obj, value, str_pool_);
      break;
    case kVpiStringVal:
      GetValueStringVal(obj, value, str_pool_);
      break;
    case kVpiTimeVal:
      value->value.integer = static_cast<int>(obj->var->value.ToUint64());
      break;
    default:
      break;
  }
}

void VpiContext::PutValue(VpiHandle obj, VpiValue* value, VpiTime* /*time*/,
                          int /*flags*/) {
  if (!obj || !value || !obj->var) return;
  if (value->format == kVpiIntVal) {
    auto new_val = static_cast<uint64_t>(value->value.integer);
    obj->var->value.words[0].aval = new_val;
    obj->var->value.words[0].bval = 0;
  } else if (value->format == kVpiRealVal) {
    auto new_val = static_cast<uint64_t>(value->value.real);
    obj->var->value.words[0].aval = new_val;
    obj->var->value.words[0].bval = 0;
  } else if (value->format == kVpiScalarVal) {
    int s = value->value.scalar;
    obj->var->value.words[0].aval = (s == kVpi1 || s == kVpiZ) ? 1 : 0;
    obj->var->value.words[0].bval = (s == kVpiX || s == kVpiZ) ? 1 : 0;
  }
}

VpiHandle VpiContext::RegisterCb(VpiCbData* data) {
  if (!data) return nullptr;
  callbacks_.push_back(*data);
  // Create a callback handle object for removal.
  auto* cb_obj = AllocObject();
  cb_obj->type = kVpiCallback;
  cb_obj->index = static_cast<int>(callbacks_.size() - 1);
  cb_handles_.push_back(cb_obj);
  return cb_obj;
}

int VpiContext::RemoveCb(VpiHandle cb_handle) {
  if (!cb_handle) return 0;
  if (cb_handle->type != kVpiCallback) return 0;
  int idx = cb_handle->index;
  if (idx >= 0 && idx < static_cast<int>(callbacks_.size())) {
    callbacks_[idx].reason = -1;  // Mark as removed.
    return 1;
  }
  return 0;
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
  switch (property) {
    case kVpiType:
      return obj->type;
    case kVpiSize:
      return obj->size;
    case kVpiDirection:
      return obj->direction;
    default:
      return 0;
  }
}

const char* VpiContext::GetStr(int property, VpiHandle obj) {
  if (!obj) return nullptr;
  switch (property) {
    case kVpiName:
      return obj->name.data();
    case kVpiFullName:
      return obj->full_name.empty() ? obj->name.data() : obj->full_name.c_str();
    case kVpiDefName:
      if (obj->type == kVpiModule) return obj->name.data();
      return nullptr;
    default:
      return nullptr;
  }
}

int VpiContext::FreeObject(VpiHandle /*obj*/) { return 0; }

int VpiContext::Control(int operation, int /*diag_level*/) {
  if (operation == kVpiFinish) {
    finish_requested_ = true;
    return 1;
  }
  if (operation == kVpiStop) {
    stop_requested_ = true;
    return 1;
  }
  return 0;
}

bool VpiContext::ChkError(VpiErrorInfo* info) {
  if (!info) return last_error_.level != 0;
  *info = last_error_;
  return last_error_.level != 0;
}

void VpiContext::GetVlogInfo(VpiVlogInfo* info) {
  if (!info) return;
  info->argc = 0;
  info->argv = nullptr;
  info->product = product_.c_str();
  info->version = version_.c_str();
}

VpiHandle VpiContext::HandleMulti(int type, VpiHandle ref1, VpiHandle ref2) {
  if (!ref1 && !ref2) return nullptr;
  // Create an iterator-like object containing children of both refs.
  auto* result = AllocObject();
  result->type = type;
  if (ref1) {
    for (auto* child : ref1->children) {
      if (child->type == type) result->children.push_back(child);
    }
  }
  if (ref2) {
    for (auto* child : ref2->children) {
      if (child->type == type) result->children.push_back(child);
    }
  }
  if (result->children.empty()) return nullptr;
  return result;
}

VpiHandle VpiContext::CreateModule(std::string_view name,
                                   std::string full_name) {
  auto* obj = AllocObject();
  obj->type = kVpiModule;
  obj->name = name;
  obj->full_name = std::move(full_name);
  object_map_[name] = obj;
  return obj;
}

VpiHandle VpiContext::CreatePort(std::string_view name, int direction,
                                 VpiHandle parent) {
  auto* obj = AllocObject();
  obj->type = kVpiPort;
  obj->name = name;
  obj->direction = direction;
  obj->parent = parent;
  if (parent) {
    obj->index = static_cast<int>(parent->children.size());
    parent->children.push_back(obj);
  }
  object_map_[name] = obj;
  return obj;
}

VpiHandle VpiContext::CreateParameter(std::string_view name, int int_value) {
  auto* obj = AllocObject();
  obj->type = kVpiParameter;
  obj->name = name;
  obj->size = int_value;  // Store param value in size field for simplicity.
  object_map_[name] = obj;
  return obj;
}

VpiHandle VpiContext::CreateNetObj(std::string_view name, Net* net_ptr,
                                   int width) {
  auto* obj = AllocObject();
  obj->type = kVpiNet;
  obj->name = name;
  obj->net = net_ptr;
  obj->size = width;
  if (net_ptr && net_ptr->resolved) obj->var = net_ptr->resolved;
  object_map_[name] = obj;
  return obj;
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

vpiHandle VpiHandleC(int type, vpiHandle ref) {
  return delta::GetGlobalVpiContext().Handle(type, ref);
}

vpiHandle vpi_handle_by_name(const char* name, vpiHandle scope) {
  return delta::GetGlobalVpiContext().HandleByName(name, scope);
}

vpiHandle VpiHandleByIndexC(vpiHandle parent, int index) {
  return delta::GetGlobalVpiContext().HandleByIndex(index, parent);
}

vpiHandle VpiHandleMultiC(int type, vpiHandle ref1, vpiHandle ref2) {
  return delta::GetGlobalVpiContext().HandleMulti(type, ref1, ref2);
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

vpiHandle vpi_put_value(vpiHandle obj, s_vpi_value* value, s_vpi_time* time,
                        int flags) {
  delta::GetGlobalVpiContext().PutValue(obj, value, time, flags);
  return obj;
}

vpiHandle vpi_register_cb(s_cb_data* data) {
  return delta::GetGlobalVpiContext().RegisterCb(data);
}

int VpiRemoveCbC(vpiHandle cb_handle) {
  return delta::GetGlobalVpiContext().RemoveCb(cb_handle);
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

int VpiControlC(int operation, ...) {
  va_list args;
  va_start(args, operation);
  int diag_level = va_arg(args, int);
  va_end(args);
  return delta::GetGlobalVpiContext().Control(operation, diag_level);
}

int VpiChkErrorC(SVpiErrorInfo* info) {
  return delta::GetGlobalVpiContext().ChkError(info) ? 1 : 0;
}

void vpi_get_vlog_info(SVpiVlogInfo* info) {
  delta::GetGlobalVpiContext().GetVlogInfo(info);
}
