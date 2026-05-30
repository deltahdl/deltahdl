#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"

namespace delta {

class SimContext;
class Scheduler;
struct Net;
struct Variable;

constexpr int kVpiModule = 32;
constexpr int kVpiNet = 36;
constexpr int kVpiReg = 48;
constexpr int kVpiPort = 44;
constexpr int kVpiParameter = 41;
constexpr int kVpiCallback = 107;

constexpr int kVpiBinStrVal = 1;
constexpr int kVpiOctStrVal = 2;
constexpr int kVpiHexStrVal = 3;
constexpr int kVpiScalarVal = 4;
constexpr int kVpiIntVal = 5;
constexpr int kVpiRealVal = 6;
constexpr int kVpiStringVal = 7;
constexpr int kVpiTimeVal = 8;
constexpr int kVpiVectorVal = 9;

constexpr int kVpiSimTime = 1;
constexpr int kVpiScaledRealTime = 2;

constexpr int kCbValueChange = 1;
constexpr int kCbReadWriteSynch = 2;
constexpr int kCbEndOfSimulation = 3;
constexpr int kCbStmt = 4;
constexpr int kCbAtStartOfSimTime = 5;
constexpr int kCbReadOnlySynch = 6;

constexpr int kCbAfterDelay = 7;
constexpr int kCbNextSimTime = 8;
constexpr int kCbNBASynch = 9;
constexpr int kCbAtEndOfSimTime = 10;

// §38.36.3: simulator action callbacks name reasons that every VPI-compliant
// tool provides (kCbEndOfSimulation above is also an action reason); simulator
// feature callbacks name optional, tool-specific reasons such as save, restart,
// reset, and interactive-mode transitions. They are registered through the same
// vpi_register_cb() path as every other callback reason.
constexpr int kCbEndOfCompile = 11;
constexpr int kCbStartOfSimulation = 12;
constexpr int kCbError = 13;
constexpr int kCbPLIError = 14;
constexpr int kCbTchkViolation = 15;
constexpr int kCbSignal = 16;
constexpr int kCbStartOfSave = 17;
constexpr int kCbEndOfSave = 18;
constexpr int kCbStartOfRestart = 19;
constexpr int kCbEndOfRestart = 20;
constexpr int kCbStartOfReset = 21;
constexpr int kCbEndOfReset = 22;
constexpr int kCbEnterInteractive = 23;
constexpr int kCbExitInteractive = 24;
constexpr int kCbInteractiveScopeChange = 25;
constexpr int kCbUnresolvedSystf = 26;

constexpr int kVpiType = 1;
constexpr int kVpiName = 2;
constexpr int kVpiFullName = 3;
constexpr int kVpiSize = 4;
constexpr int kVpiDirection = 5;
constexpr int kVpiDefName = 6;

constexpr int kVpiLibrary = 67;
constexpr int kVpiConfig = 70;
constexpr int kVpiCell = 71;

constexpr int kVpiInput = 1;
constexpr int kVpiOutput = 2;
constexpr int kVpiInout = 3;

constexpr int kVpiNoDelay = 1;
constexpr int kVpiInertialDelay = 2;
constexpr int kVpiTransportDelay = 3;
constexpr int kVpiPureTransportDelay = 4;

constexpr int kVpiFinish = 66;
constexpr int kVpiStop = 67;
// §38.36.3: a reset can be requested indirectly through vpi_control(vpiReset).
constexpr int kVpiReset = 68;

constexpr int kVpi0 = 0;
constexpr int kVpi1 = 1;
constexpr int kVpiX = 2;
constexpr int kVpiZ = 3;

constexpr int kVpiNotice = 1;
constexpr int kVpiWarning = 2;
constexpr int kVpiError = 3;
constexpr int kVpiInternal = 4;

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

  std::string library_name;
  std::string cell_name;
  std::string config_name;

  std::vector<VpiObject*> children;
  size_t scan_index = 0;
};

using VpiHandle = VpiObject*;

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

struct VpiTime {
  int type = 0;
  uint32_t high = 0;
  uint32_t low = 0;
  double real = 0.0;
};

struct VpiCbData {
  int reason = 0;
  // §38.36 (Figure 38-17): the application routine the simulator invokes when it
  // executes the callback; it is passed a pointer to this s_cb_data structure.
  int (*cb_rtn)(VpiCbData*) = nullptr;
  VpiHandle obj = nullptr;
  VpiTime* time = nullptr;
  VpiValue* value = nullptr;
  int index = 0;
  void* user_data = nullptr;
};

struct VpiErrorInfo {
  int state = 0;
  int level = 0;
  const char* message = nullptr;
  const char* product = nullptr;
  const char* code = nullptr;
  const char* file = nullptr;
  int line = 0;
};

struct VpiVlogInfo {
  int argc = 0;
  const char** argv = nullptr;
  const char* product = nullptr;
  const char* version = nullptr;
};

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

class VpiContext {
 public:
  VpiContext() = default;
  ~VpiContext();

  void Attach(SimContext& sim_ctx);

  void SetScheduler(Scheduler* sched) { scheduler_ = sched; }

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
  int ExecuteCallback(VpiHandle cb_handle);
  void RegisterCbValueChange(const VpiCbData& data);

  // §38.36.3: deliver every active callback registered for the given action or
  // feature reason. Each routine receives a copy of its s_cb_data whose reason
  // field holds the reason for the callback; when a non-null obj or user_data is
  // supplied the simulator fills that field before the routine runs (for
  // example, the timing-check handle for cbTchkViolation, the new scope handle
  // for cbInteractiveScopeChange, or the unresolved name for cbUnresolvedSystf).
  // Returns how many callbacks were delivered.
  int DispatchCallbacks(int reason, VpiHandle obj = nullptr,
                        void* user_data = nullptr);

  // §38.36.3: a reset delivers cbStartOfReset at the start of the operation and
  // cbEndOfReset once it has completed. This is the single path used whether the
  // reset was requested directly or through vpi_control(vpiReset, ...).
  int DispatchReset();

  // §38.36.3: a restart first removes every registered callback except the
  // restart callbacks, then delivers cbStartOfRestart followed by cbEndOfRestart,
  // so the only callbacks that exist across a restart are those two.
  int DispatchRestart();

  int Get(int property, VpiHandle obj);
  const char* GetStr(int property, VpiHandle obj);
  int FreeObject(VpiHandle obj);
  int Control(int operation, int diag_level);
  bool ChkError(VpiErrorInfo* info);
  void GetVlogInfo(VpiVlogInfo* info);
  VpiHandle HandleMulti(int type, VpiHandle ref1, VpiHandle ref2);

  VpiHandle CreateModule(std::string_view name, std::string full_name);

  VpiHandle CreatePort(std::string_view name, int direction, VpiHandle parent);

  VpiHandle CreateParameter(std::string_view name, int int_value);

  VpiHandle CreateNetObj(std::string_view name, Net* net_ptr, int width);

  const std::vector<VpiSystfData>& RegisteredSystfs() const { return systfs_; }

  const std::vector<VpiCbData>& RegisteredCallbacks() const {
    return callbacks_;
  }

  // §36.9.1: the registration of system tasks shall occur prior to elaboration
  // or the resolution of references. Marking elaboration as started closes the
  // window in which RegisterSystf will accept new registrations.
  void MarkElaborationStarted() { elaboration_started_ = true; }
  bool ElaborationStarted() const { return elaboration_started_; }

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
  Scheduler* scheduler_ = nullptr;
  bool elaboration_started_ = false;
  bool stop_requested_ = false;
  bool finish_requested_ = false;
  VpiErrorInfo last_error_ = {};
  std::string product_ = "DeltaHDL";
  std::string version_ = "0.1.0";

  std::vector<std::string> str_pool_;
};

Region RegionForPliCallback(int reason);

bool IsOneShotPliCallback(int reason);

VpiContext& GetGlobalVpiContext();
void SetGlobalVpiContext(VpiContext* ctx);

// §36.9.1: the intended use model places a reference to a registration
// routine in the vlog_startup_routines[] array. Each entry is a function that
// takes no arguments and returns nothing, and the array is conventionally
// null-terminated.
using VlogStartupRoutine = void (*)();

// §36.9.1: walking the vlog_startup_routines[] array calls each non-null
// entry in order, giving each routine its chance to register user-defined
// system tasks and functions before elaboration begins. Iteration stops at
// the first null sentinel.
void InvokeVlogStartupRoutines(VlogStartupRoutine* routines);

}

using vpiHandle = delta::VpiHandle;
using s_vpi_value = delta::VpiValue;
using s_vpi_time = delta::VpiTime;
using s_cb_data = delta::VpiCbData;
using s_vpi_systf_data = delta::VpiSystfData;
using s_vpi_vecval = delta::VpiVectorVal;
using SVpiErrorInfo = delta::VpiErrorInfo;
using SVpiVlogInfo = delta::VpiVlogInfo;

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
#define cbReadOnlySynch 6
#define cbAfterDelay 7
#define cbNextSimTime 8
#define cbNBASynch 9
#define cbAtEndOfSimTime 10

// §38.36.3 simulator action/feature callback reasons (mirror of the kCb* values).
#define cbEndOfCompile 11
#define cbStartOfSimulation 12
#define cbError 13
#define cbPLIError 14
#define cbTchkViolation 15
#define cbSignal 16
#define cbStartOfSave 17
#define cbEndOfSave 18
#define cbStartOfRestart 19
#define cbEndOfRestart 20
#define cbStartOfReset 21
#define cbEndOfReset 22
#define cbEnterInteractive 23
#define cbExitInteractive 24
#define cbInteractiveScopeChange 25
#define cbUnresolvedSystf 26

#define vpiType 1
#define vpiName 2
#define vpiFullName 3
#define vpiSize 4
#define vpiDirection 5
#define vpiDefName 6
#define vpiLibrary 67
#define vpiConfig 70
#define vpiCell 71

#define vpiInput 1
#define vpiOutput 2
#define vpiInout 3

#define vpiNoDelay 1
#define vpiInertialDelay 2
#define vpiTransportDelay 3
#define vpiPureTransportDelay 4

#define vpiFinish 66
#define vpiStop 67
#define vpiReset 68

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
