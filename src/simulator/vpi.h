#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

namespace delta {

class SimContext;
struct Net;
struct Variable;

// --- VPI object type constants (IEEE 1800-2023 Section 36.12) ---

constexpr int kVpiModule = 32;
constexpr int kVpiNet = 36;
constexpr int kVpiReg = 48;
constexpr int kVpiPort = 44;
constexpr int kVpiParameter = 41;
constexpr int kVpiCallback = 107;

// --- VPI value format constants (IEEE 1800-2023 Section 36.18) ---

constexpr int kVpiBinStrVal = 1;
constexpr int kVpiOctStrVal = 2;
constexpr int kVpiHexStrVal = 3;
constexpr int kVpiScalarVal = 4;
constexpr int kVpiIntVal = 5;
constexpr int kVpiRealVal = 6;
constexpr int kVpiStringVal = 7;
constexpr int kVpiTimeVal = 8;
constexpr int kVpiVectorVal = 9;

// --- VPI time type constants (IEEE 1800-2023 Section 36.17) ---

constexpr int kVpiSimTime = 1;
constexpr int kVpiScaledRealTime = 2;

// --- VPI callback reason constants (IEEE 1800-2023 Section 36.20) ---

constexpr int kCbValueChange = 1;
constexpr int kCbReadWriteSynch = 2;
constexpr int kCbEndOfSimulation = 3;
constexpr int kCbStmt = 4;
constexpr int kCbAtStartOfSimTime = 5;

// --- VPI property constants (IEEE 1800-2023 Section 36.13) ---

constexpr int kVpiType = 1;
constexpr int kVpiName = 2;
constexpr int kVpiFullName = 3;
constexpr int kVpiSize = 4;
constexpr int kVpiDirection = 5;
constexpr int kVpiDefName = 6;

// --- VPI direction constants (IEEE 1800-2023 Section 36.13) ---

constexpr int kVpiInput = 1;
constexpr int kVpiOutput = 2;
constexpr int kVpiInout = 3;

// --- VPI put_value delay mode constants (IEEE 1800-2023 Section 36.19) ---

constexpr int kVpiNoDelay = 1;
constexpr int kVpiInertialDelay = 2;
constexpr int kVpiTransportDelay = 3;
constexpr int kVpiPureTransportDelay = 4;

// --- VPI control constants (IEEE 1800-2023 Section 36.34) ---

constexpr int kVpiFinish = 66;
constexpr int kVpiStop = 67;

// --- VPI scalar value constants (IEEE 1800-2023 Section 36.18) ---

constexpr int kVpi0 = 0;
constexpr int kVpi1 = 1;
constexpr int kVpiX = 2;
constexpr int kVpiZ = 3;

// --- VPI error severity (IEEE 1800-2023 Section 36.33) ---

constexpr int kVpiNotice = 1;
constexpr int kVpiWarning = 2;
constexpr int kVpiError = 3;
constexpr int kVpiInternal = 4;

// --- VPI object definition ---

struct VpiObject {
  int type = 0;
  std::string_view name;
  std::string full_name;
  Variable* var = nullptr;
  Net* net = nullptr;
  VpiObject* parent = nullptr;
  int direction = 0;
  int size = 0;
  int index = 0;
  // Iterator state.
  std::vector<VpiObject*> children;
  size_t scan_index = 0;
};

using VpiHandle = VpiObject*;

// --- VPI value struct (IEEE 1800-2023 Section 36.18) ---

struct VpiVectorVal {
  uint32_t aval;
  uint32_t bval;
};

struct VpiValue {
  int format = 0;
  union {
    int integer;
    double real;
    const char* str;
    int scalar;
    VpiVectorVal* vector;
  } value = {};
};

// --- VPI time struct (IEEE 1800-2023 Section 36.17) ---

struct VpiTime {
  int type = 0;
  uint32_t high = 0;
  uint32_t low = 0;
  double real = 0.0;
};

// --- VPI callback data (IEEE 1800-2023 Section 36.20) ---

struct VpiCbData {
  int reason = 0;
  VpiHandle obj = nullptr;
  VpiTime* time = nullptr;
  VpiValue* value = nullptr;
  int index = 0;
  void* user_data = nullptr;
};

// --- VPI error info (IEEE 1800-2023 Section 36.33) ---

struct VpiErrorInfo {
  int state = 0;
  int level = 0;
  const char* message = nullptr;
  const char* product = nullptr;
  const char* code = nullptr;
  const char* file = nullptr;
  int line = 0;
};

// --- VPI vlog info (IEEE 1800-2023 Section 36.32) ---

struct VpiVlogInfo {
  int argc = 0;
  const char** argv = nullptr;
  const char* product = nullptr;
  const char* version = nullptr;
};

// --- VPI system task/function data (IEEE 1800-2023 Section 36.7) ---

constexpr int kVpiSysTask = 1;
constexpr int kVpiSysFunc = 2;

struct VpiSystfData {
  int type = 0;
  int sysfunctype = 0;
  const char* tfname = nullptr;
  int (*calltf)(const char*) = nullptr;
  int (*compiletf)(const char*) = nullptr;
  int (*sizetf)(const char*) = nullptr;
  void* user_data = nullptr;
};

// --- VPI context ---

class VpiContext {
 public:
  VpiContext() = default;
  ~VpiContext();

  void Attach(SimContext& sim_ctx);

  VpiHandle RegisterSystf(VpiSystfData* data);
  VpiHandle HandleByName(const char* name, VpiHandle scope);
  VpiHandle HandleByIndex(int index, VpiHandle parent);
  VpiHandle Handle(int type, VpiHandle ref);
  VpiHandle Iterate(int type, VpiHandle ref);
  VpiHandle Scan(VpiHandle iterator);
  void GetValue(VpiHandle obj, VpiValue* value);
  void PutValue(VpiHandle obj, VpiValue* value, VpiTime* time, int flags);
  VpiHandle RegisterCb(VpiCbData* data);
  int RemoveCb(VpiHandle cb_handle);
  void RegisterCbValueChange(const VpiCbData& data);
  int Get(int property, VpiHandle obj);
  const char* GetStr(int property, VpiHandle obj);
  int FreeObject(VpiHandle obj);
  int Control(int operation, int diag_level);
  bool ChkError(VpiErrorInfo* info);
  void GetVlogInfo(VpiVlogInfo* info);
  VpiHandle HandleMulti(int type, VpiHandle ref1, VpiHandle ref2);

  // Create a module-type VPI object (used during elaboration).
  VpiHandle CreateModule(std::string_view name, std::string full_name);

  // Create a port-type VPI object under a parent module.
  VpiHandle CreatePort(std::string_view name, int direction, VpiHandle parent);

  // Create a parameter-type VPI object.
  VpiHandle CreateParameter(std::string_view name, int int_value);

  // Create a net-type VPI object.
  VpiHandle CreateNetObj(std::string_view name, Net* net_ptr, int width);

  const std::vector<VpiSystfData>& RegisteredSystfs() const { return systfs_; }

  const std::vector<VpiCbData>& RegisteredCallbacks() const {
    return callbacks_;
  }

  bool StopRequested() const { return stop_requested_; }
  bool FinishRequested() const { return finish_requested_; }

  const VpiErrorInfo& LastError() const { return last_error_; }

 private:
  VpiHandle AllocObject();

  std::vector<VpiSystfData> systfs_;
  std::vector<VpiCbData> callbacks_;
  std::vector<VpiHandle> cb_handles_;
  std::unordered_map<std::string_view, VpiObject*> object_map_;
  std::vector<VpiObject*> all_objects_;
  bool stop_requested_ = false;
  bool finish_requested_ = false;
  VpiErrorInfo last_error_ = {};
  std::string product_ = "DeltaHDL";
  std::string version_ = "0.1.0";
  // Storage for string values returned by GetStr / GetValue.
  std::vector<std::string> str_pool_;
};

// --- Global VPI context access ---

VpiContext& GetGlobalVpiContext();
void SetGlobalVpiContext(VpiContext* ctx);

}  // namespace delta

// =============================================================================
// C API (IEEE 1800-2023 Sections 36-39)
//
// The VPI C API names below are MANDATED by IEEE Std 1800-2023. They use
// snake_case functions, s_-prefixed structs, and camelCase constants as
// defined in the standard. These names cannot be changed. Exceptions for
// these names are configured in .clang-tidy (FunctionIgnoredRegexp,
// TypeAliasIgnoredRegexp).
// =============================================================================

// Type aliases [IEEE 1800-2023 §36.6].
using vpiHandle = delta::VpiHandle;
using s_vpi_value = delta::VpiValue;
using s_vpi_time = delta::VpiTime;
using s_cb_data = delta::VpiCbData;
using s_vpi_systf_data = delta::VpiSystfData;
using s_vpi_vecval = delta::VpiVectorVal;
using SVpiErrorInfo = delta::VpiErrorInfo;
using SVpiVlogInfo = delta::VpiVlogInfo;

// VPI constants [IEEE 1800-2023 §36.12, §36.17, §36.18, §36.20].
// Defined as macros per IEEE convention (vpi_user.h uses #define).
#define vpiModule 32
#define vpiNet 36
#define vpiReg 48
#define vpiPort 44
#define vpiParameter 41
#define vpiCallback 107

#define vpiBinStrVal 1
#define vpiOctStrVal 2
#define vpiHexStrVal 3
#define vpiScalarVal 4
#define vpiIntVal 5
#define vpiRealVal 6
#define vpiStringVal 7
#define vpiTimeVal 8
#define vpiVectorVal 9

#define vpiSimTime 1
#define vpiScaledRealTime 2

#define cbValueChange 1
#define cbReadWriteSynch 2
#define cbEndOfSimulation 3
#define cbStmt 4
#define cbAtStartOfSimTime 5

#define vpiType 1
#define vpiName 2
#define vpiFullName 3
#define vpiSize 4
#define vpiDirection 5
#define vpiDefName 6

#define vpiInput 1
#define vpiOutput 2
#define vpiInout 3

#define vpiNoDelay 1
#define vpiInertialDelay 2
#define vpiTransportDelay 3
#define vpiPureTransportDelay 4

#define vpiFinish 66
#define vpiStop 67

#define vpi0 0
#define vpi1 1
#define vpiX 2
#define vpiZ 3

#define vpiNotice 1
#define vpiWarning 2
#define vpiError 3
#define vpiInternal 4

#define vpiSysTask 1
#define vpiSysFunc 2

// VPI C API function declarations [IEEE 1800-2023 §36.7-§36.34].
vpiHandle vpi_register_systf(s_vpi_systf_data* data);
vpiHandle VpiHandleC(int type, vpiHandle ref);
vpiHandle vpi_handle_by_name(const char* name, vpiHandle scope);
vpiHandle VpiHandleByIndexC(vpiHandle parent, int index);
vpiHandle VpiHandleMultiC(int type, vpiHandle ref1, vpiHandle ref2);
vpiHandle vpi_iterate(int type, vpiHandle ref);
vpiHandle vpi_scan(vpiHandle iterator);
void vpi_get_value(vpiHandle obj, s_vpi_value* value);
vpiHandle vpi_put_value(vpiHandle obj, s_vpi_value* value, s_vpi_time* time,
                        int flags);
vpiHandle vpi_register_cb(s_cb_data* data);
int VpiRemoveCbC(vpiHandle cb_handle);
int vpi_get(int property, vpiHandle obj);
const char* vpi_get_str(int property, vpiHandle obj);
int vpi_free_object(vpiHandle obj);
int VpiControlC(int operation, ...);
int VpiChkErrorC(SVpiErrorInfo* info);
void vpi_get_vlog_info(SVpiVlogInfo* info);
