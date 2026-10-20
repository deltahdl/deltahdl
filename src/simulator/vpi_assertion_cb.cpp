#include "simulator/vpi_assertion_cb.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "simulator/assertion_api.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §39.4.2: the routine is given a pointer to the callback's time - the model
// keeps a time as
// one 64-bit count of simulation time units, and s_vpi_time carries it in the
// two halves vpiSimTime names.
s_vpi_time VpiAssertionCallbackTime(std::uint64_t model_time) {
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.high = static_cast<std::uint32_t>(model_time >> 32);
  time.low = static_cast<std::uint32_t>(model_time & 0xFFFFFFFFU);
  return time;
}

// §39.4.2: the expression the assertion `assertion` holds whose source text
// is `text`, found over the objects its expression or its property spec hangs
// below it; null where it holds none. A net or variable an operand names is
// its scope's, and what that object holds is no part of the assertion.
VpiObject* ExpressionWritten(VpiObject* assertion, std::string_view text) {
  if (text.empty()) return nullptr;
  VpiContext& vpi = GetGlobalVpiContext();
  std::vector<VpiObject*> pending(assertion->children.rbegin(),
                                  assertion->children.rend());
  std::unordered_set<const VpiObject*> seen;
  while (!pending.empty()) {
    VpiObject* obj = pending.back();
    pending.pop_back();
    if (obj == nullptr || !seen.insert(obj).second) continue;
    const char* written = vpi.GetStrRaw(vpiDecompile, obj);
    if (written != nullptr && text == written) return obj;
    if (VpiIsVariablesType(obj->type) || VpiIsNetsType(obj->type)) continue;
    pending.insert(pending.end(), obj->children.rbegin(), obj->children.rend());
  }
  return nullptr;
}

// §39.4.2: call the application's routine with the five arguments the clause
// lists - the reason, a pointer to the time of the callback, the handle for the
// assertion, a pointer to an attempt information structure, and the user data
// supplied when the callback was registered.
//
// The attempt information follows the clause's own rule about when there is
// any: a lock, unlock, disable, enable, reset, kill, pass action, fail action,
// vacuous action or nonvacuous action callback is given a NULL
// p_vpi_attempt_info pointer, which is what the model reports through the args
// it delivers, and attemptStartTime is what fills it. A failure callback's
// detail is the failExpr, and a step callback's the step: the expressions it
// matched and the states it went from and to. The model holds each expression
// as the source text the run read it by, which names the object of the
// assertion that decompiles to it.
void VpiCallAssertionRoutine(vpi_assertion_callback_func* cb_rtn,
                             VpiHandle assertion,
                             const AssertionCallbackArgs& args) {
  s_vpi_time cb_time = VpiAssertionCallbackTime(args.cb_time);
  s_vpi_attempt_info info = {};
  p_vpi_attempt_info info_p = nullptr;
  s_vpi_assertion_step_info step = {};
  std::vector<vpiHandle> matched;
  if (args.info != nullptr) {
    info.attemptStartTime =
        VpiAssertionCallbackTime(args.info->attempt_start_time);
    info_p = &info;
    if (args.reason == cbAssertionFailure) {
      info.detail.failExpr =
          VpiHandleOf(ExpressionWritten(assertion, args.info->fail_expr));
    } else if (args.reason == cbAssertionStepSuccess ||
               args.reason == cbAssertionStepFailure) {
      for (const std::string& text : args.info->step.matched_exprs) {
        matched.push_back(VpiHandleOf(ExpressionWritten(assertion, text)));
      }
      step.matched_expression_count = static_cast<PLI_INT32>(matched.size());
      step.matched_exprs = matched.empty() ? nullptr : matched.data();
      step.stateFrom = args.info->step.state_from;
      step.stateTo = args.info->step.state_to;
      info.detail.step = &step;
    }
  }
  cb_rtn(args.reason, &cb_time, VpiHandleOf(assertion), info_p,
         static_cast<PLI_BYTE8*>(args.user_data));
}

// §20.11: what an assertion control task selects the assertion `obj` by. Its
// kind gives its Table 20-6 assertion_type bit -- concurrent, or a simple,
// observed deferred or final deferred immediate assertion -- and its Table 20-7
// directive_type bit; a restrict has none (§16.14.4).
AssertionControlTarget ControlTargetOf(const VpiObject& obj) {
  struct KindBits {
    int type;
    uint32_t type_bit;
    uint32_t directive_bit;
  };
  static constexpr KindBits kKinds[] = {
      {vpiAssert, 1, 1},          {vpiCover, 1, 2},
      {vpiAssume, 1, 4},          {vpiRestrict, 1, 0},
      {vpiImmediateAssert, 2, 1}, {vpiImmediateCover, 2, 2},
      {vpiImmediateAssume, 2, 4}};
  AssertionControlTarget target;
  for (const KindBits& kind : kKinds) {
    if (kind.type != obj.type) continue;
    target.type_bit = kind.type_bit;
    target.directive_bit = kind.directive_bit;
  }
  if (obj.is_deferred) target.type_bit = obj.is_final ? 8 : 4;
  if (obj.parent != nullptr) target.scope = obj.parent->full_name;
  target.full_name = obj.full_name;
  return target;
}

}  // namespace

std::string VpiAssertionKeyOf(const VpiObject& obj) {
  if (!obj.full_name.empty()) return obj.full_name;
  if (!obj.name.empty()) return std::string(obj.name);
  // The scope is the nearest enclosing object with a full name; a procedure
  // or a statement the assertion stands under has none.
  const VpiObject* scope = obj.parent;
  while (scope != nullptr && scope->full_name.empty()) scope = scope->parent;
  return AssertionKey(scope != nullptr ? scope->full_name : "", {},
                      static_cast<uint32_t>(obj.start_line),
                      static_cast<uint32_t>(obj.column));
}

VpiHandle VpiRegisterAssertionCb(VpiHandle assertion, int reason,
                                 vpi_assertion_callback_func* cb_rtn,
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
  const std::string kKey = VpiAssertionKeyOf(*assertion);
  AssertionCallbackHandle placed = api.PlaceAssertionCallback(
      reason, kKey, assertion->type,
      [cb_rtn, assertion](const AssertionCallbackArgs& args) {
        VpiCallAssertionRoutine(cb_rtn, assertion, args);
      },
      user_data);
  if (placed == 0) return nullptr;
  api.NoteControlTarget(kKey, ControlTargetOf(*assertion));

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

  // §37.2.2 a): removing a callback releases its handle, which is what stops
  // the removed callback's handle from being a live handle to its object, as it
  // does for a simulation callback.
  GetGlobalVpiContext().ReleaseHandle(cb_handle);
  return true;
}

}  // namespace delta
