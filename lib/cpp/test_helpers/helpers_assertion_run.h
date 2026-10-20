#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/assertion_api.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {

// One call of an assertion callback (§39.4.2) or an assertion system callback
// (§39.4.1) as its routine saw it: the reason, the full name of the assertion
// it was handed, empty for a system callback, its cb_time, whether it was
// given attempt information and the attempt's start time there, and the
// simulation time it ran at.
struct AssertionCall {
  int reason = 0;
  std::string assertion;
  uint64_t cb_time = 0;
  bool has_info = false;
  uint64_t attempt_start = 0;
  uint64_t now = 0;
  bool operator==(const AssertionCall&) const = default;
};

inline std::vector<AssertionCall>& AssertionCalls() {
  static std::vector<AssertionCall> calls;
  return calls;
}

// What `$arm` does when the design calls it.
inline std::function<void()>& AssertionArmer() {
  static std::function<void()> armer;
  return armer;
}

inline uint64_t AssertionTicks(const s_vpi_time& time) {
  return (uint64_t{time.high} << 32) | time.low;
}

inline uint64_t AssertionNow() {
  s_vpi_time now = {};
  now.type = vpiSimTime;
  vpi_get_time(nullptr, &now);
  return AssertionTicks(now);
}

inline PLI_INT32 RecordAssertionCall(PLI_INT32 reason, p_vpi_time cb_time,
                                     vpiHandle assertion,
                                     p_vpi_attempt_info info,
                                     PLI_BYTE8* /*user_data*/) {
  AssertionCall call;
  call.reason = reason;
  const char* name =
      assertion != nullptr ? vpi_get_str(vpiFullName, assertion) : nullptr;
  call.assertion = name == nullptr ? "" : name;
  call.cb_time = cb_time != nullptr ? AssertionTicks(*cb_time) : 0;
  call.has_info = info != nullptr;
  call.attempt_start =
      info != nullptr ? AssertionTicks(info->attemptStartTime) : 0;
  call.now = AssertionNow();
  AssertionCalls().push_back(call);
  return 0;
}

inline PLI_INT32 RecordAssertionSystemCall(p_cb_data data) {
  AssertionCall call;
  call.reason = data->reason;
  call.now = AssertionNow();
  AssertionCalls().push_back(call);
  return 0;
}

// Places a `reason` callback on the assertion `full_name` names.
inline vpiHandle WatchAssertion(const char* full_name, int reason) {
  return vpi_register_assertion_cb(
      vpi_handle_by_name(VpiText(full_name), nullptr), reason,
      &RecordAssertionCall, nullptr);
}

// Places a `reason` assertion system callback.
inline vpiHandle WatchAssertionSystem(int reason) {
  s_cb_data data = {};
  data.reason = reason;
  data.cb_rtn = &RecordAssertionSystemCall;
  return vpi_register_cb(&data);
}

// Has the design's calls of `$arm` take `steps` in turn, one a call, and the
// calls after the last do nothing.
inline void ArmInTurn(std::vector<std::function<void()>> steps) {
  AssertionArmer() = [steps = std::move(steps), next = size_t{0}]() mutable {
    if (next < steps.size()) steps[next++]();
  };
}

// The value of the integer variable `full_name`.
inline int IntOf(const char* full_name) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(vpi_handle_by_name(VpiText(full_name), nullptr), &value);
  return value.value.integer;
}

// The assert of `instance` that has no name, null for none. An instance's
// assertion iteration also reaches the unnamed property inst its spec holds
// (§37.49), which is not an assert.
inline vpiHandle UnnamedAssertOf(const char* instance) {
  vpiHandle it =
      vpi_iterate(vpiAssertion, vpi_handle_by_name(VpiText(instance), nullptr));
  while (vpiHandle obj = it == nullptr ? nullptr : vpi_scan(it)) {
    if (vpi_get(vpiType, obj) == vpiAssert &&
        vpi_get_str(vpiName, obj) == nullptr) {
      return obj;
    }
  }
  return nullptr;
}

// A run of a design whose assertions an application watches through the
// assertion API of its own case, the design calling `$arm` to place the
// case's callbacks once the model exists.
class AssertionRun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    SetGlobalAssertionApi(&api_);
    AssertionCalls().clear();
    AssertionArmer() = [] {};
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$arm");
    data.calltf = [](PLI_BYTE8*) -> PLI_INT32 {
      AssertionArmer()();
      return 0;
    };
    ASSERT_NE(vpi_register_systf(&data), nullptr);
  }
  void TearDown() override {
    SetGlobalAssertionApi(nullptr);
    VpiDesignRun::TearDown();
  }

 public:
  // The calls recorded for `reason`, in order.
  static std::vector<AssertionCall> CallsOf(int reason) {
    std::vector<AssertionCall> of;
    for (const AssertionCall& call : AssertionCalls()) {
      if (call.reason == reason) of.push_back(call);
    }
    return of;
  }

 protected:
  AssertionApi api_;
};

}  // namespace delta
