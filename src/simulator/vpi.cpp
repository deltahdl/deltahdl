#include "simulator/vpi.h"

#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string>
#include <string_view>

#include "common/types.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

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

  // §36.9.1: a user-defined system task or system function name shall begin
  // with a dollar sign. Refuse to register a name that omits the leading '$'.
  if (data->tfname == nullptr || data->tfname[0] != '$') {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "system task or function name must begin with '$'";
    return nullptr;
  }

  // §36.9.1: the registration of system tasks shall occur prior to elaboration
  // or the resolution of references. Once elaboration has begun the window has
  // closed, so reject the registration.
  if (elaboration_started_) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "system task or function registration must precede elaboration";
    return nullptr;
  }

  systfs_.push_back(*data);

  // §38.37 Returns row: registration produces a handle to the callback
  // object standing in for this system task or system function.
  auto* systf_obj = AllocObject();
  systf_obj->type = kVpiCallback;
  systf_obj->index = static_cast<int>(systfs_.size() - 1);
  return systf_obj;
}

VpiHandle VpiContext::HandleByName(const char* name, VpiHandle ) {
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

  if (ref->parent && ref->parent->type == type) return ref->parent;

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
  uint64_t bval = obj->var->value.words[0].bval;
  int width = static_cast<int>(obj->var->value.width);
  int oct_digits = (width + 2) / 3;
  std::string result;
  result.reserve(oct_digits);
  for (int i = oct_digits - 1; i >= 0; --i) {
    uint8_t a_bits = (aval >> (i * 3)) & 0x7;
    uint8_t b_bits = (bval >> (i * 3)) & 0x7;
    if (b_bits != 0) {
      // §38.15, Table 38-3 (octal row): a digit covering any unknown bit is
      // reported as z only when the whole group is z, otherwise as x.
      result += (b_bits == 0x7 && a_bits == 0x7) ? 'z' : 'x';
    } else {
      result += static_cast<char>('0' + a_bits);
    }
  }
  pool.push_back(std::move(result));
  value->value.str = pool.back().c_str();
}

static int ScalarFromBits(uint64_t aval, uint64_t bval) {
  if (!bval) return aval ? kVpi1 : kVpi0;
  return aval ? kVpiZ : kVpiX;
}

static void GetValueVector(VpiHandle obj, VpiValue* value,
                           std::vector<std::vector<VpiVectorVal>>& pool) {
  const auto& v = obj->var->value;
  int width = static_cast<int>(v.width);
  // §38.15: the vector value occupies an array of s_vpi_vecval whose size is
  // ((vector_size - 1) / 32 + 1), one element per 32 bits of the vector.
  int array_size = width > 0 ? ((width - 1) / 32 + 1) : 1;
  std::vector<VpiVectorVal> vec(static_cast<size_t>(array_size));
  for (int i = 0; i < array_size; ++i) {
    // Internal four-state words are 64 bits wide, so two vecval elements map
    // onto each word: the LSB of the vector lands in element 0, bit 33 in the
    // LSB of element 1, and so on.
    int word_idx = i / 2;
    int shift = (i % 2) * 32;
    uint64_t aval = word_idx < static_cast<int>(v.nwords)
                        ? v.words[word_idx].aval
                        : 0;
    uint64_t bval = word_idx < static_cast<int>(v.nwords)
                        ? v.words[word_idx].bval
                        : 0;
    auto a32 = static_cast<uint32_t>((aval >> shift) & 0xFFFFFFFFu);
    auto b32 = static_cast<uint32_t>((bval >> shift) & 0xFFFFFFFFu);
    // §38.15 / Figure 38-8: the returned encoding is ab 00=0, 10=1, 11=X,
    // 01=Z. That assigns the aval bit of an unknown the opposite sense from
    // the internal word (X is a=0/b=1, Z is a=1/b=1), so flip the aval bit of
    // every unknown position by xoring in the bval bits.
    vec[static_cast<size_t>(i)].aval = a32 ^ b32;
    vec[static_cast<size_t>(i)].bval = b32;
  }
  pool.push_back(std::move(vec));
  value->value.vector = pool.back().data();
}

static void GetValueStrength(VpiHandle obj, VpiValue* value,
                             std::vector<std::vector<VpiStrengthVal>>& pool) {
  const auto& v = obj->var->value;
  int width = static_cast<int>(v.width);
  if (width < 1) width = 1;
  // §38.15: the strength arm holds one descriptor per bit of the vector.
  std::vector<VpiStrengthVal> arr(static_cast<size_t>(width));
  for (int i = 0; i < width; ++i) {
    int word_idx = i / 64;
    int bit = i % 64;
    uint64_t aval =
        word_idx < static_cast<int>(v.nwords) ? v.words[word_idx].aval : 0;
    uint64_t bval =
        word_idx < static_cast<int>(v.nwords) ? v.words[word_idx].bval : 0;
    arr[static_cast<size_t>(i)].logic =
        ScalarFromBits((aval >> bit) & 1, (bval >> bit) & 1);
    // §38.15: a reg or variable is always reported at strong strength, so both
    // the 0 and 1 drive components carry the strong-drive code.
    arr[static_cast<size_t>(i)].s0 = vpiStrongDrive;
    arr[static_cast<size_t>(i)].s1 = vpiStrongDrive;
  }
  pool.push_back(std::move(arr));
  value->value.strength = pool.back().data();
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
    case kVpiIntVal: {
      // §38.15, Table 38-3: any x or z bit of the object maps to a 0 in the
      // returned integer, so drop every unknown bit before handing it back.
      uint64_t aval = obj->var->value.words[0].aval;
      uint64_t bval = obj->var->value.words[0].bval;
      value->value.integer = static_cast<int>(aval & ~bval);
      break;
    }
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
    case kVpiVectorVal:
      GetValueVector(obj, value, vec_pool_);
      break;
    case kVpiStrengthVal:
      GetValueStrength(obj, value, strength_pool_);
      break;
    case kVpiObjTypeVal: {
      // §38.15: fill in the value and rewrite the format field to the closest
      // format for the object's type. A real object reports vpiRealVal, a
      // single-bit object is a scalar, and anything wider is a vector.
      const auto& v = obj->var->value;
      if (v.is_real) {
        value->format = kVpiRealVal;
        value->value.real = static_cast<double>(v.ToUint64());
      } else if (v.width == 1) {
        value->format = kVpiScalarVal;
        value->value.scalar =
            ScalarFromBits(v.words[0].aval & 1, v.words[0].bval & 1);
      } else {
        value->format = kVpiVectorVal;
        GetValueVector(obj, value, vec_pool_);
      }
      break;
    }
    default:
      break;
  }
}

void VpiContext::PutValue(VpiHandle obj, VpiValue* value, VpiTime* ,
                          int ) {
  if (!obj || !value) return;
  if (!obj->var && !obj->net) return;

  if (scheduler_) scheduler_->NoteWriteAttempt();
  if (!obj->var) return;
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
    callbacks_[idx].reason = -1;
    return 1;
  }
  return 0;
}

int VpiContext::ExecuteCallback(VpiHandle cb_handle) {
  if (!cb_handle || cb_handle->type != kVpiCallback) return 0;
  int idx = cb_handle->index;
  if (idx < 0 || idx >= static_cast<int>(callbacks_.size())) return 0;
  VpiCbData& cb = callbacks_[idx];
  // §38.36: the simulator executes the callback by invoking the cb_rtn the
  // application supplied, passing it a pointer to the s_cb_data structure (which
  // belongs to the simulator). With no cb_rtn there is nothing to invoke.
  if (!cb.cb_rtn) return 0;
  return cb.cb_rtn(&cb);
}

void VpiContext::RegisterCbValueChange(const VpiCbData& data) {
  if (!data.obj || !data.obj->var) return;
  void* user_data = data.user_data;
  data.obj->var->AddWatcher([user_data]() {
    if (user_data) *static_cast<bool*>(user_data) = true;
    return true;
  });
}

int VpiContext::DispatchCallbacks(int reason, VpiHandle obj, void* user_data) {
  int fired = 0;
  // §38.36.3: only callbacks still registered for this reason are delivered.
  // RemoveCb marks a removed callback by clearing its reason, so a removed slot
  // never matches a real reason here. Snapshot the count so callbacks registered
  // from within a routine are not delivered during this same pass.
  size_t count = callbacks_.size();
  for (size_t i = 0; i < count; ++i) {
    if (callbacks_[i].reason != reason || callbacks_[i].cb_rtn == nullptr) {
      continue;
    }
    // §38.36.3: the routine is passed a pointer to an s_cb_data structure that
    // is not the one supplied at registration. Work from a copy and let the
    // simulator fill obj/user_data when it has them for this reason.
    VpiCbData data = callbacks_[i];
    if (obj != nullptr) {
      data.obj = obj;
    }
    if (user_data != nullptr) {
      data.user_data = user_data;
    }
    data.cb_rtn(&data);
    ++fired;
  }
  return fired;
}

int VpiContext::DispatchReset() {
  int fired = DispatchCallbacks(kCbStartOfReset);
  fired += DispatchCallbacks(kCbEndOfReset);
  return fired;
}

int VpiContext::DispatchRestart() {
  // §38.36.3: with the exception of the restart callbacks, every registered
  // callback is removed when a restart occurs. Clearing the reason marks a slot
  // removed, matching RemoveCb.
  for (VpiCbData& slot : callbacks_) {
    if (slot.reason != kCbStartOfRestart && slot.reason != kCbEndOfRestart) {
      slot.reason = -1;
    }
  }
  int fired = DispatchCallbacks(kCbStartOfRestart);
  fired += DispatchCallbacks(kCbEndOfRestart);
  return fired;
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

    case kVpiLibrary:
      if (obj->type != kVpiModule) return nullptr;
      return obj->library_name.c_str();
    case kVpiCell:
      if (obj->type != kVpiModule) return nullptr;
      return obj->cell_name.empty() ? obj->name.data() : obj->cell_name.c_str();
    case kVpiConfig:
      if (obj->type != kVpiModule) return nullptr;
      return obj->config_name.c_str();
    default:
      return nullptr;
  }
}

int VpiContext::FreeObject(VpiHandle ) { return 0; }

int VpiContext::Control(int operation, int ) {
  if (operation == kVpiFinish) {
    finish_requested_ = true;
    return 1;
  }
  if (operation == kVpiStop) {
    stop_requested_ = true;
    return 1;
  }
  // §38.36.3: a reset requested through vpi_control(vpiReset, ...) drives the
  // same reset-callback sequence as a directly invoked $reset, so route it
  // through the one DispatchReset path.
  if (operation == kVpiReset) {
    DispatchReset();
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
  obj->size = int_value;
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

Region RegionForPliCallback(int reason) {
  switch (reason) {
    case kCbAfterDelay:
    case kCbNextSimTime:
    case kCbAtStartOfSimTime:
      return Region::kPreActive;

    case kCbReadWriteSynch:
    case kCbNBASynch:
      return Region::kPreNBA;
    case kCbAtEndOfSimTime:
      return Region::kPrePostponed;
    case kCbReadOnlySynch:
      return Region::kPostponed;
    default:
      return Region::kCOUNT;
  }
}

bool IsOneShotPliCallback(int reason) {
  return RegionForPliCallback(reason) != Region::kCOUNT;
}

static VpiContext* g_vpi_context = nullptr;
static VpiContext g_default_context;

VpiContext& GetGlobalVpiContext() {
  if (g_vpi_context) return *g_vpi_context;
  return g_default_context;
}

void SetGlobalVpiContext(VpiContext* ctx) { g_vpi_context = ctx; }

void InvokeVlogStartupRoutines(VlogStartupRoutine* routines) {
  if (!routines) return;
  for (size_t i = 0; routines[i] != nullptr; ++i) {
    routines[i]();
  }
}

}

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
