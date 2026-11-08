#pragma once

#include <cstdint>

#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

constexpr int kVpiSysTask = vpiSysTask;
constexpr int kVpiSysFunc = vpiSysFunc;

constexpr int kVpiIntFunc = vpiIntFunc;
constexpr int kVpiRealFunc = vpiRealFunc;
constexpr int kVpiTimeFunc = vpiTimeFunc;
constexpr int kVpiSizedFunc = vpiSizedFunc;
constexpr int kVpiSizedSignedFunc = vpiSizedSignedFunc;

constexpr int kVpiDefaultSizedFuncBits = 32;

enum class VpiSystfCallback : std::uint8_t { kCompiletf, kSizetf, kCalltf };

bool VpiSystfNameIsValid(const char* tfname);

int VpiSystfReturnType(const s_vpi_systf_data& data);

bool VpiSystfCallbackFiresAtBuild(VpiSystfCallback callback);

int VpiSystfInvoke(PLI_INT32 (*routine)(PLI_BYTE8*), PLI_BYTE8* user_data);

bool VpiSystfSizetfIsCalled(const s_vpi_systf_data& data);

int VpiSystfResultSizeBits(const s_vpi_systf_data& data);

enum class VpiToolPhase : std::uint8_t { kStartup, kSizetf, kFull };

bool VpiPhaseRestrictsFunctionality(VpiToolPhase phase);

enum class VpiRoutine : std::uint8_t {
  kRegisterSystf,
  kRegisterCb,
  kGetValue,
  kPutValue,
  kIterate,
};

bool VpiRoutineAvailableInStartup(VpiRoutine routine);

bool VpiStartupCallbackReasonAllowed(int reason);

bool VpiIsSimulationTimeCallbackReason(int reason);

bool VpiHasAccessByIndex(int type);

bool VpiIndexesItsVarBits(const VpiObject& obj);

VpiObject* VpiVarBitAt(const VpiObject& obj, int index);

int VpiGenScopeArraySize(VpiHandle gen_scope_array);

struct VpiTimeQueueSlot {
  uint64_t time = 0;
  bool is_current = false;
  bool has_events_before_read_only_synch = false;
};

}  // namespace delta
