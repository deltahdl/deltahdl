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
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

s_vpi_time VpiAssertionCallbackTime(std::uint64_t model_time) {
  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.high = static_cast<std::uint32_t>(model_time >> 32);
  time.low = static_cast<std::uint32_t>(model_time & 0xFFFFFFFFU);
  return time;
}

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
  const VpiObject* scope = obj.parent;
  while (scope != nullptr && scope->full_name.empty()) scope = scope->parent;
  return AssertionKey(scope != nullptr ? scope->full_name : "", {},
                      static_cast<uint32_t>(obj.start_line),
                      static_cast<uint32_t>(obj.column));
}

VpiHandle VpiLabelledAssertionOr(VpiHandle found) {
  if (found->type != vpiNamedBegin) return found;
  for (VpiObject* child : found->children) {
    if (VpiIsAssertionType(child->type) &&
        child->full_name == found->full_name) {
      return child;
    }
  }
  return found;
}

VpiHandle VpiLabelledAssertionsBeginOr(VpiHandle found) {
  VpiObject* begin = found->parent;
  if (VpiIsAssertionType(found->type) && begin != nullptr &&
      begin->type == vpiNamedBegin && begin->full_name == found->full_name) {
    return begin;
  }
  return found;
}

VpiHandle VpiRegisterAssertionCb(VpiHandle assertion, int reason,
                                 vpi_assertion_callback_func* cb_rtn,
                                 PLI_BYTE8* user_data) {
  if (assertion == nullptr || cb_rtn == nullptr) return nullptr;

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
  if (cb_handle == nullptr || !cb_handle->is_assertion_cb) return false;
  if (!GetGlobalAssertionApi().RemoveAssertionCallback(
          cb_handle->assertion_cb_handle)) {
    return false;
  }

  GetGlobalVpiContext().ReleaseHandle(cb_handle);
  return true;
}

}  // namespace delta
