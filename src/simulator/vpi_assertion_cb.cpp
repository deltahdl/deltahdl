#include "simulator/vpi_assertion_cb.h"

#include <cstdint>

#include "simulator/vpi.h"

namespace delta {
namespace {

AssertionApi* g_assertion_api = nullptr;

// §39.4.2: "A pointer to the time of the callback" - the model keeps a time as
// one 64-bit count of simulation time units, and s_vpi_time carries it in the
// two halves vpiSimTime names.
s_vpi_time VpiAssertionCallbackTime(std::uint64_t model_time) {
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.high = static_cast<std::uint32_t>(model_time >> 32);
  time.low = static_cast<std::uint32_t>(model_time & 0xFFFFFFFFU);
  return time;
}

// §39.4.2: call the application's routine with the five arguments the clause
// lists - the reason, a pointer to the time of the callback, the handle for the
// assertion, a pointer to an attempt information structure, and the user data
// supplied when the callback was registered.
//
// The attempt information follows the clause's own rule about when there is
// any: "On lock, unlock, disable, enable, reset, kill, pass action, fail
// action, vacuous action, and nonvacuous action callbacks, the returned
// p_vpi_attempt_info info pointer is NULL", which is what the model reports
// through the args it delivers, and attemptStartTime is what fills it. The
// detail union is left as the clause leaves it for a start or success callback,
// where only attemptStartTime is valid: the expressions a failure or a step
// carries are held by the model as the source text of the expression rather
// than as objects, so there is no handle to put in failExpr or in a step's
// expression array until the run's assertion engine drives this API.
void VpiCallAssertionRoutine(vpi_assertion_callback_func cb_rtn,
                             VpiHandle assertion,
                             const AssertionCallbackArgs& args) {
  s_vpi_time cb_time = VpiAssertionCallbackTime(args.cb_time);
  s_vpi_attempt_info info = {};
  p_vpi_attempt_info info_p = nullptr;
  if (args.info != nullptr) {
    info.attempt_start_time =
        VpiAssertionCallbackTime(args.info->attempt_start_time);
    info_p = &info;
  }
  cb_rtn(args.reason, &cb_time, assertion, info_p,
         static_cast<PLI_BYTE8*>(args.user_data));
}

}  // namespace

AssertionApi& GetGlobalAssertionApi() {
  // Function-local static: the default model is constructed on first use rather
  // than during static init, matching GetGlobalVpiContext().
  static AssertionApi default_api;
  if (g_assertion_api != nullptr) return *g_assertion_api;
  return default_api;
}

void SetGlobalAssertionApi(AssertionApi* api) { g_assertion_api = api; }

VpiHandle VpiRegisterAssertionCb(VpiHandle assertion, int reason,
                                 vpi_assertion_callback_func cb_rtn,
                                 PLI_BYTE8* user_data) {
  // §39.4.2: the placement names an assertion and a routine to call on it.
  // Neither is optional - a placement with no assertion has nothing to be
  // specific to, and one with no routine has nothing to call each time the
  // event occurs - so either missing is an error on placing the callback, which
  // the clause answers with a NULL handle.
  if (assertion == nullptr || cb_rtn == nullptr) return nullptr;

  // §39.4.2: which reasons may be placed on which handle is the model's rule -
  // every reason on a concurrent or immediate assertion, and cbAssertionStart,
  // cbAssertionSuccess and cbAssertionFailure also on a sequence or property
  // instance. A reason the assertion cannot carry is an error on placing, and
  // the placement answers with the NULL handle for it.
  AssertionApi& api = GetGlobalAssertionApi();
  AssertionCallbackHandle placed = api.PlaceAssertionCallback(
      reason, assertion->name, assertion->type,
      [cb_rtn, assertion](const AssertionCallbackArgs& args) {
        VpiCallAssertionRoutine(cb_rtn, assertion, args);
      },
      user_data);
  if (placed == 0) return nullptr;

  return GetGlobalVpiContext().CreateAssertionCallbackObject(placed);
}

bool VpiRemoveAssertionCb(VpiHandle cb_handle) {
  // §39.4.2: only the handle a placement answered with names a placed assertion
  // callback. Anything else - a null handle, or the handle of a simulation
  // callback - is left to vpi_remove_cb()'s own removal.
  if (cb_handle == nullptr || !cb_handle->is_assertion_cb) return false;
  if (!GetGlobalAssertionApi().RemoveAssertionCallback(
          cb_handle->assertion_cb_handle)) {
    return false;
  }

  // §37.2.2 a): "vpi_remove_callback() releases the associated callback
  // handle", which is what stops the removed callback's handle from being a
  // live handle to its object, as it does for a simulation callback.
  GetGlobalVpiContext().ReleaseHandle(cb_handle);
  return true;
}

}  // namespace delta
