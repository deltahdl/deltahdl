#include <cstddef>
#include <cstdio>
#include <fstream>
#include <functional>
#include <optional>
#include <sstream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "simulator/coverage_control.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_control_requests.h"
#include "simulator/vpi_coverage.h"
#include "simulator/vpi_coverage_items.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

static void OnRoutineReturn(VpiControlRequests& control,
                            std::function<void()> task) {
  if (control.routines_running > 0) {
    control.on_return.push_back(std::move(task));
    return;
  }
  task();
}

static void EndRunAsRequested(SimContext* sim, bool finish, int level) {
  if (sim == nullptr) return;
  EmitFinishDiagnostic(*sim, finish ? "$finish" : "$stop", level, sim->Out());
  sim->RequestFinish();
}

void VpiContext::LeaveApplicationRoutine() {
  if (--control_.routines_running > 0) return;
  std::vector<std::function<void()>> requested;
  requested.swap(control_.on_return);
  for (const std::function<void()>& task : requested) task();
}

int VpiContext::Control(int operation, int arg0, VpiHandle scope) {
  if (operation == kVpiFinish || operation == kVpiStop) {
    const bool kFinish = operation == kVpiFinish;
    (kFinish ? control_.finish_requested : control_.stop_requested) = true;
    (kFinish ? control_.finish_diag_level : control_.stop_diag_level) = arg0;
    OnRoutineReturn(control_, [this, kFinish, arg0] {
      EndRunAsRequested(sim_ctx_, kFinish, arg0);
    });
    return 1;
  }
  if (operation == kVpiSetInteractiveScope) {
    if (scope == nullptr || !VpiIsScopeObject(scope)) return 0;
    NoteInteractiveScope(scope);
    return 1;
  }
  return 0;
}

void VpiContext::NoteInteractiveScope(VpiHandle scope) {
  control_.interactive_scope = scope;
  if (sim_ctx_ != nullptr) sim_ctx_->SetInteractiveScope(scope->full_name);
  DispatchCallbacks(kCbInteractiveScopeChange, scope);
}

namespace {

CoverageControl CoverageControlForOperation(int operation) {
  switch (operation) {
    case vpiCoverageStart:
      return CoverageControl::kStart;
    case vpiCoverageStop:
      return CoverageControl::kStop;
    case vpiCoverageReset:
      return CoverageControl::kReset;
    case vpiCoverageCheck:
      return CoverageControl::kCheck;
    default:
      return CoverageControl::kStart;
  }
}

}  // namespace

std::string CoverageScopeName(const VpiObject* scope_handle) {
  if (scope_handle == nullptr || (!VpiIsInstanceType(scope_handle->type) &&
                                  !VpiIsAssertionType(scope_handle->type))) {
    return std::string();
  }
  if (!scope_handle->full_name.empty()) return scope_handle->full_name;
  return std::string(scope_handle->name);
}

std::optional<int> CoverageTypeForVpiProperty(int property) {
  switch (property) {
    case vpiAssertCoverage:
      return kCoverageTypeAssertion;
    case vpiFsmStateCoverage:
      return kCoverageTypeFsmState;
    case vpiStatementCoverage:
      return kCoverageTypeStatement;
    case vpiToggleCoverage:
      return kCoverageTypeToggle;
    default:
      return std::nullopt;
  }
}

CoverageControlState& VpiContext::GetCoverageControlState() {
  if (sim_ctx_ != nullptr) return sim_ctx_->GetCoverageControlState();
  return coverage_control_;
}

int VpiContext::ControlCoverage(int operation, int coverage_type,
                                VpiHandle scope_handle,
                                const std::string& name) {
  switch (operation) {
    case vpiCoverageStart:
    case vpiCoverageStop:
    case vpiCoverageReset:
    case vpiCoverageCheck: {
      CoverageControl control = CoverageControlForOperation(operation);
      if (scope_handle != nullptr && VpiIsAssertionType(scope_handle->type)) {
        return VpiControlAssertionCoverage(
            control, coverage_type, *scope_handle, GetCoverageControlState());
      }
      std::string scope = CoverageScopeName(scope_handle);
      return static_cast<int>(GetCoverageControlState().Control(
          control,
          CoverageTypeForVpiProperty(coverage_type).value_or(coverage_type),
          scope));
    }
    case vpiCoverageSave:
      return static_cast<int>(GetCoverageControlState().CoverageSave(
          CoverageTypeForVpiProperty(coverage_type).value_or(coverage_type),
          name));
    case vpiCoverageMerge:
      return static_cast<int>(GetCoverageControlState().CoverageMerge(
          CoverageTypeForVpiProperty(coverage_type).value_or(coverage_type),
          name));
    default:
      return 0;
  }
}

bool VpiContext::ChkError(s_vpi_error_info* info) {
  if (!info) return last_error_.level != 0;
  *info = last_error_;
  return last_error_.level != 0;
}

void VpiContext::SetInvocationArguments(
    const std::string& tool_name, const std::vector<std::string>& options) {
  invocation_args_.clear();
  invocation_args_.reserve(options.size() + 1);
  invocation_args_.push_back(tool_name);
  for (const std::string& option : options) invocation_args_.push_back(option);
}

namespace {

constexpr std::string_view kVpiVendorOptionsFileFlag = "-f";

constexpr int kVpiMaxOptionsFileDepth = 16;

struct VpiArgvEntry {
  size_t word = 0;
  int nested_array = -1;
};
struct VpiArgvArray {
  std::vector<VpiArgvEntry> entries;
  size_t offset = 0;
};

std::vector<std::string> VpiOptionsFileWords(const std::string& path) {
  std::vector<std::string> words;
  std::ifstream ifs(path);
  if (!ifs) return words;
  std::string line;
  while (std::getline(ifs, line)) {
    std::istringstream words_of_line(line);
    std::string word;
    while (words_of_line >> word) {
      if (!word.empty() && word[0] == '#') break;
      words.push_back(std::move(word));
    }
  }
  return words;
}

int VpiBuildArgvArray(const std::vector<std::string>& words, int depth,
                      std::vector<std::string>* pool,
                      std::vector<VpiArgvArray>* arrays) {
  int self = static_cast<int>(arrays->size());
  arrays->emplace_back();
  for (size_t i = 0; i < words.size(); ++i) {
    pool->push_back(words[i]);
    (*arrays)[static_cast<size_t>(self)].entries.push_back(
        {pool->size() - 1, -1});
    const bool kNamesFile = words[i] == kVpiVendorOptionsFileFlag &&
                            i + 1 < words.size() &&
                            depth < kVpiMaxOptionsFileDepth;
    if (!kNamesFile) continue;
    std::vector<std::string> nested = {words[i + 1]};
    for (std::string& word : VpiOptionsFileWords(words[i + 1])) {
      nested.push_back(std::move(word));
    }
    int child = VpiBuildArgvArray(nested, depth + 1, pool, arrays);
    (*arrays)[static_cast<size_t>(self)].entries.push_back({0, child});
    ++i;
  }
  return self;
}

void VpiPlaceArgvArrays(std::vector<std::string>& pool,
                        std::vector<VpiArgvArray>* arrays,
                        std::vector<PLI_BYTE8*>* argv) {
  size_t offset = 0;
  for (size_t k = 0; k < arrays->size(); ++k) {
    (*arrays)[k].offset = offset;
    offset += (*arrays)[k].entries.size() + (k == 0 ? 0 : 1);
  }
  argv->assign(offset, nullptr);
  for (const VpiArgvArray& array : *arrays) {
    size_t at = array.offset;
    for (const VpiArgvEntry& entry : array.entries) {
      if (entry.nested_array < 0) (*argv)[at] = pool[entry.word].data();
      ++at;
    }
  }
}

void VpiLinkArgvArrays(const std::vector<VpiArgvArray>& arrays,
                       std::vector<PLI_BYTE8*>* argv) {
  for (const VpiArgvArray& array : arrays) {
    size_t at = array.offset;
    for (const VpiArgvEntry& entry : array.entries) {
      if (entry.nested_array >= 0) {
        PLI_BYTE8** nested =
            argv->data() +
            arrays[static_cast<size_t>(entry.nested_array)].offset;
        (*argv)[at] = reinterpret_cast<PLI_BYTE8*>(nested);
      }
      ++at;
    }
  }
}

}  // namespace

bool VpiContext::GetVlogInfo(s_vpi_vlog_info* info) {
  if (!info) return false;

  invocation_file_args_.clear();
  std::vector<VpiArgvArray> arrays;
  VpiBuildArgvArray(invocation_args_, 0, &invocation_file_args_, &arrays);
  VpiPlaceArgvArrays(invocation_file_args_, &arrays, &invocation_argv_);
  VpiLinkArgvArrays(arrays, &invocation_argv_);

  info->argc = static_cast<int>(arrays.empty() ? 0 : arrays[0].entries.size());
  info->argv = invocation_argv_.empty() ? nullptr : invocation_argv_.data();
  info->product = VpiText(product_.data());
  info->version = version_.data();
  return true;
}

namespace {

bool InterModPathSizeMismatch(int type, VpiHandle ref1, VpiHandle ref2) {
  return type == vpiInterModPath && ref1->size != ref2->size;
}

bool IsChildOf(VpiHandle ref, const VpiObject* obj) {
  for (auto* child : ref->children) {
    if (child == obj) return true;
  }
  return false;
}

VpiObject* ObjectSharedBy(VpiHandle ref1, VpiHandle ref2, int type) {
  if (!ref1 || !ref2) return nullptr;
  for (auto* child : ref1->children) {
    if (child->type != type) continue;
    if (!IsChildOf(ref2, child)) continue;
    return child;
  }
  return nullptr;
}

}  // namespace

VpiHandle VpiContext::HandleMulti(int type, VpiHandle ref1, VpiHandle ref2) {
  if (!ref1 || !ref2) return nullptr;

  if (InterModPathSizeMismatch(type, ref1, ref2)) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "vpi_handle_multi(): the two ports of an intermodule path must be of "
        "the same size");
    return nullptr;
  }

  return ObjectSharedBy(ref1, ref2, type);
}

VpiObject* VpiResolveSameObject(VpiObject* obj) {
  for (int steps = 0; obj && obj->same_object_as && steps < 1000; ++steps) {
    obj = obj->same_object_as;
  }
  return obj;
}

VpiHandle VpiContext::CreateHandleFor(VpiHandle object) {
  if (object == nullptr) return nullptr;

  VpiObject* rep = VpiResolveSameObject(object);

  if (!rep->object_exists) return nullptr;

  auto* handle = AllocObject();
  handle->type = rep->type;

  handle->same_object_as = rep;
  return handle;
}

void VpiContext::ReleaseHandle(VpiHandle handle) {
  if (!handle) return;
  if (handle->handles_held > 1) {
    --handle->handles_held;
    return;
  }
  handle->handles_held = 0;
  handle->released = true;
}

PLI_INT32 VpiContext::ReleaseHandleStatus(VpiHandle handle) {
  if (!HandleValid(handle)) return 0;

  if (handle->type == vpiIterator) {
    delete handle;
    return 1;
  }

  ReleaseHandle(handle);
  return 1;
}

bool VpiContext::HandleReleased(VpiHandle handle) const {
  return handle != nullptr && handle->released;
}

bool VpiContext::HandleValid(VpiHandle handle) const {
  if (!handle) return false;
  if (handle->released) return false;

  return VpiResolveSameObject(handle)->object_exists;
}

bool VpiContext::HandleSurvivesRestart(VpiHandle handle) const {
  if (!handle || handle->type != kVpiCallback) return false;
  if (handle->index < 0 ||
      handle->index >= static_cast<int>(callbacks_.size())) {
    return false;
  }
  int reason = callbacks_[handle->index].reason;
  return reason == kCbStartOfRestart || reason == kCbEndOfRestart;
}

void VpiContext::ReleaseHandlesForRestart() {
  for (VpiObject* handle : all_objects_) {
    if (!HandleSurvivesRestart(handle)) handle->released = true;
  }
}

void VpiContext::ReleaseHandleWithCallbacks(VpiObject* object) {
  if (!object) return;
  object->released = true;
  for (VpiObject* cb : cb_handles_) {
    if (cb->index >= 0 && cb->index < static_cast<int>(callbacks_.size()) &&
        CompareObjects(VpiObjectOf(callbacks_[cb->index].obj), object) != 0) {
      cb->released = true;
    }
  }
}

void VpiContext::ReleaseHandleSubtree(VpiObject* root) {
  if (!root) return;
  ReleaseHandleWithCallbacks(root);
  for (VpiObject* child : root->children) {
    if (child->type != vpiThread && child->type != vpiClassDefn) {
      ReleaseHandleSubtree(child);
    }
  }
}

void VpiContext::ReleaseFrameOrThreadObject(VpiHandle root) {
  if (root == nullptr) return;
  if (root->type == vpiFrame) DispatchCallbacks(cbEndOfFrame, root);
  if (root->type == vpiThread) DispatchCallbacks(cbEndOfThread, root);

  ReleaseHandleSubtree(root);
}

void VpiContext::ReleaseClassObject(VpiHandle class_object) {
  if (!class_object) return;
  DispatchCallbacks(cbReclaimObj, class_object);
  DispatchCallbacks(cbEndOfObject, class_object);

  ReleaseHandleWithCallbacks(class_object);
  for (VpiObject* member : class_object->children) {
    if (member->automatic && !VpiIsClassMethodType(member->type)) {
      ReleaseHandleSubtree(member);
    }
  }
}

bool VpiContext::SetDefaultCompatibilityMode(int mode) {
  if (default_compat_mode_selected_ && mode != default_compat_mode_) {
    return false;
  }
  default_compat_mode_ = mode;
  default_compat_mode_selected_ = true;
  return true;
}

int VpiContext::EffectiveCompatibilityMode(bool uses_mechanism1,
                                           int mechanism1_mode) const {
  if (uses_mechanism1) {
    return mechanism1_mode;
  }
  return default_compat_mode_;
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

VpiHandle VpiContext::CreateAssertion(std::string_view name, int type) {
  auto* obj = AllocObject();
  obj->type = type;
  obj->name = name;
  if (!name.empty()) object_map_[name] = obj;
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

VpiHandle VpiContext::CreateRegArray(
    std::string_view name, int array_type,
    const std::vector<std::vector<int>>& dim_indices,
    const std::vector<Variable*>& elements) {
  auto* obj = AllocObject();
  obj->type = vpiRegArray;
  obj->name = name;
  obj->array_type = array_type;
  obj->array_dim_indices = dim_indices;
  obj->size = static_cast<int>(elements.size());
  for (size_t i = 0; i < elements.size(); ++i) {
    auto* child = AllocObject();
    child->type = kVpiReg;
    child->var = elements[i];
    child->parent = obj;
    child->index = static_cast<int>(i);
    if (elements[i]) child->size = static_cast<int>(elements[i]->value.width);
    obj->children.push_back(child);
  }
  if (!name.empty()) object_map_[name] = obj;
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

VpiContext& GetGlobalVpiContext() {
  static VpiContext default_context;
  if (g_vpi_context) return *g_vpi_context;
  return default_context;
}

void SetGlobalVpiContext(VpiContext* ctx) { g_vpi_context = ctx; }

void InvokeVlogStartupRoutines(VlogStartupRoutine* routines) {
  if (!routines) return;
  VpiContext& ctx = GetGlobalVpiContext();
  VpiToolPhase prior = ctx.ToolPhase();
  ctx.SetToolPhase(VpiToolPhase::kStartup);
  for (size_t i = 0; routines[i] != nullptr; ++i) {
    routines[i]();
  }
  ctx.SetToolPhase(prior);
}

bool VpiPhaseRestrictsFunctionality(VpiToolPhase phase) {
  return phase != VpiToolPhase::kFull;
}

bool VpiContext::RoutineIsUnavailableNow(VpiRoutine routine) {
  if (!VpiPhaseRestrictsFunctionality(tool_phase_)) return false;
  if (VpiRoutineAvailableInStartup(routine)) return false;
  last_error_.state = kVpiPLI;
  last_error_.level = kVpiError;
  last_error_.message = VpiText(
      "VPI routine is not available until cbEndOfCompile; only "
      "vpi_register_systf() and vpi_register_cb() may be called before then");
  return true;
}

bool VpiRoutineAvailableInStartup(VpiRoutine routine) {
  return routine == VpiRoutine::kRegisterSystf ||
         routine == VpiRoutine::kRegisterCb;
}

bool VpiStartupCallbackReasonAllowed(int reason) {
  switch (reason) {
    case kCbEndOfCompile:
    case kCbStartOfSimulation:
    case kCbEndOfSimulation:
    case kCbUnresolvedSystf:
    case kCbError:
    case kCbPLIError:
      return true;
    default:
      return false;
  }
}

bool VpiIsSimulationTimeCallbackReason(int reason) {
  switch (reason) {
    case kCbAtStartOfSimTime:
    case kCbNBASynch:
    case kCbReadWriteSynch:
    case kCbAtEndOfSimTime:
    case kCbReadOnlySynch:
    case kCbNextSimTime:
    case kCbAfterDelay:
      return true;
    default:
      return false;
  }
}

bool VpiSystfNameIsValid(const char* tfname) {
  if (tfname == nullptr || tfname[0] != '$' || tfname[1] == '\0') return false;
  for (const char* p = tfname + 1; *p != '\0'; ++p) {
    char c = *p;
    bool legal = (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
                 (c >= '0' && c <= '9') || c == '_' || c == '$';
    if (!legal) return false;
  }
  return true;
}

int VpiSystfReturnType(const s_vpi_systf_data& data) {
  if (data.type != kVpiSysFunc) return 0;
  return data.sysfunctype;
}

bool VpiSystfCallbackFiresAtBuild(VpiSystfCallback callback) {
  return callback == VpiSystfCallback::kCompiletf ||
         callback == VpiSystfCallback::kSizetf;
}

int VpiSystfInvoke(PLI_INT32 (*routine)(PLI_BYTE8*), PLI_BYTE8* user_data) {
  if (routine == nullptr) return 0;
  return routine(user_data);
}

bool VpiSystfSizetfIsCalled(const s_vpi_systf_data& data) {
  return data.type == kVpiSysFunc && (data.sysfunctype == kVpiSizedFunc ||
                                      data.sysfunctype == kVpiSizedSignedFunc);
}

int VpiContext::SystfResultSizeBits(const s_vpi_systf_data& data) {
  for (size_t i = 0; i < systfs_.size(); ++i) {
    if (&systfs_[i] != &data) continue;
    auto it = systf_result_bits_.find(i);
    if (it != systf_result_bits_.end()) return it->second;
    int bits = VpiSystfResultSizeBits(data);
    systf_result_bits_.emplace(i, bits);
    return bits;
  }
  return VpiSystfResultSizeBits(data);
}

int VpiSystfResultSizeBits(const s_vpi_systf_data& data) {
  if (VpiSystfSizetfIsCalled(data) && data.sizetf != nullptr) {
    return VpiSystfInvoke(data.sizetf, data.user_data);
  }
  if (data.type == kVpiSysFunc &&
      (data.sysfunctype == vpiTimeFunc || data.sysfunctype == vpiRealFunc)) {
    return 64;
  }
  return kVpiDefaultSizedFuncBits;
}

}  // namespace delta
