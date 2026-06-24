#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/dpi.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"

namespace delta {

int VpiContext::Control(int operation, int arg0, int arg1, int arg2,
                        VpiHandle scope) {
  // §38.4: vpiFinish/vpiStop request the matching built-in task on return of
  // the application routine and carry its diagnostic message level (see 20.2).
  if (operation == kVpiFinish) {
    finish_requested_ = true;
    finish_diag_level_ = arg0;
    return 1;
  }
  if (operation == kVpiStop) {
    stop_requested_ = true;
    stop_diag_level_ = arg0;
    return 1;
  }
  // §38.4: vpiReset requests $reset and is passed three additional integer
  // arguments (stop_value, reset_value, diagnostics_value), the same values the
  // $reset task takes (see D.8). Record them, then route through the one
  // DispatchReset path so the reset-callback sequence (§38.36.3) runs exactly
  // as it does for a directly invoked $reset.
  if (operation == kVpiReset) {
    reset_requested_ = true;
    reset_stop_value_ = arg0;
    reset_reset_value_ = arg1;
    reset_diag_value_ = arg2;
    DispatchReset();
    return 1;
  }
  // §38.4: vpiSetInteractiveScope immediately retargets the tool's interactive
  // scope to the supplied vpiScope handle.
  if (operation == kVpiSetInteractiveScope) {
    interactive_scope_ = scope;
    return 1;
  }
  return 0;
}

namespace {

// §40.5.3: map a Start/Stop/Reset/Check coverage-control operation onto the
// matching CoverageControl request.
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

// The handle names the controlled scope. A handle's hierarchical name
// identifies the instance; a handle with no full name falls back to its simple
// name. A null handle names no scope, which the control rules treat as a
// nonexisting scope (a bad argument).
std::string CoverageScopeName(VpiHandle scope_handle) {
  std::string scope;
  if (scope_handle != nullptr) {
    if (!scope_handle->full_name.empty()) {
      scope = scope_handle->full_name;
    } else {
      scope = std::string(scope_handle->name);
    }
  }
  return scope;
}

}  // namespace

int VpiContext::ControlCoverage(int operation, int coverage_type,
                                VpiHandle scope_handle,
                                const std::string& name) {
  switch (operation) {
    case vpiCoverageStart:
    case vpiCoverageStop:
    case vpiCoverageReset:
    case vpiCoverageCheck: {
      // §40.5.3: Start/Stop/Reset/Check control the collection of coverage over
      // a scope, with the semantics of $coverage_control() (§40.3.2.1). The
      // coverage type selects the kind of coverage being controlled but, since
      // statement, toggle, and FSM coverage are not individually controllable,
      // the control acts on the instance (or assertion) the handle names as a
      // whole rather than on any sub-object of it.
      CoverageControl control = CoverageControlForOperation(operation);
      std::string scope = CoverageScopeName(scope_handle);
      return static_cast<int>(coverage_control_.Control(control, scope));
    }
    case vpiCoverageSave:
      // §40.5.3: save the current coverage of the requested type to the named
      // coverage database, per $coverage_save() (§40.3.2.5).
      return static_cast<int>(
          coverage_control_.CoverageSave(coverage_type, name));
    case vpiCoverageMerge:
      // §40.5.3: merge coverage of the requested type from the named coverage
      // database into the simulation, per $coverage_merge() (§40.3.2.4).
      return static_cast<int>(
          coverage_control_.CoverageMerge(coverage_type, name));
    default:
      // Not a coverage control operation: nothing to apply.
      return 0;
  }
}

bool VpiContext::ChkError(VpiErrorInfo* info) {
  if (!info) return last_error_.level != 0;
  *info = last_error_;
  return last_error_.level != 0;
}

void VpiContext::SetInvocationArguments(
    const std::string& tool_name, const std::vector<std::string>& options) {
  // §38.17: entry zero of the command line is the tool's own name; the
  // invocation options follow it in order.
  invocation_args_.clear();
  invocation_args_.reserve(options.size() + 1);
  invocation_args_.push_back(tool_name);
  for (const std::string& option : options) invocation_args_.push_back(option);
}

bool VpiContext::GetVlogInfo(VpiVlogInfo* info) {
  // §38.17: a null result structure cannot receive the information, so the
  // routine fails.
  if (!info) return false;

  // §38.17: rebuild the argv pointer array so each entry references a
  // NUL-terminated copy of one command-line token (std::string guarantees the
  // terminator). There are argc entries, and entry zero is the tool name -
  // both guaranteed by how invocation_args_ was populated.
  invocation_argv_.clear();
  invocation_argv_.reserve(invocation_args_.size());
  for (const std::string& arg : invocation_args_) {
    invocation_argv_.push_back(arg.c_str());
  }

  info->argc = static_cast<int>(invocation_argv_.size());
  info->argv = invocation_argv_.empty() ? nullptr : invocation_argv_.data();
  info->product = product_.c_str();
  info->version = version_.c_str();
  return true;
}

namespace {

// §38.22: a request for an intermodule path names the output-port and
// input-port reference objects the path runs between. Those two ports shall be
// of the same size; they may, however, sit at different levels of the
// hierarchy, which is deliberately left unconstrained. A size mismatch cannot
// describe a valid intermodule path, so it is rejected by the caller.
bool InterModPathSizeMismatch(int type, VpiHandle ref1, VpiHandle ref2) {
  return type == vpiInterModPath && ref1 && ref2 && ref1->size != ref2->size;
}

// Append every child of `ref` whose kind matches `type` to `out`. A null `ref`
// contributes nothing.
void CollectChildrenOfType(VpiHandle ref, int type,
                           std::vector<VpiObject*>& out) {
  if (!ref) return;
  for (auto* child : ref->children) {
    if (child->type == type) out.push_back(child);
  }
}

}  // namespace

VpiHandle VpiContext::HandleMulti(int type, VpiHandle ref1, VpiHandle ref2) {
  if (!ref1 && !ref2) return nullptr;

  if (InterModPathSizeMismatch(type, ref1, ref2)) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_handle_multi(): the two ports of an intermodule path must be of "
        "the same size";
    return nullptr;
  }

  auto* result = AllocObject();
  result->type = type;
  CollectChildrenOfType(ref1, type, result->children);
  CollectChildrenOfType(ref2, type, result->children);
  if (result->children.empty()) return nullptr;
  return result;
}

// §38.3: resolve a handle to the representative of the underlying simulation
// object it denotes by following the same_object_as chain. A bounded walk
// guards against an accidental cycle; the chains the simulator builds are short
// (a handle aliases at most one representative).
static VpiObject* ResolveSameObject(VpiObject* obj) {
  for (int steps = 0; obj && obj->same_object_as && steps < 1000; ++steps) {
    obj = obj->same_object_as;
  }
  return obj;
}

int VpiContext::CompareObjects(VpiHandle obj1, VpiHandle obj2) {
  // §38.3: a null handle names no object, so it can never refer to the same
  // object as anything.
  if (obj1 == nullptr || obj2 == nullptr) return 0;

  VpiObject* a = ResolveSameObject(obj1);
  VpiObject* b = ResolveSameObject(obj2);

  // §38.3: the comparison holds only "provided that the simulation object
  // exists". A handle whose underlying object is absent (e.g. a class handle
  // that is still null) is never equal to anything, even to itself.
  if (!a->object_exists || !b->object_exists) return 0;

  // §38.3: TRUE when both handles resolve to the same underlying object. The
  // representatives are compared, not the original handle pointers, so two
  // distinct handles that alias one object still compare equal - object
  // equivalence cannot be settled by a C "==" of the handles.
  return a == b ? 1 : 0;
}

VpiHandle VpiContext::CreateHandleFor(VpiHandle object) {
  // §37.2.1: a null object denotes nothing, so there is no handle to create.
  if (object == nullptr) return nullptr;

  // Resolve through any existing alias chain to the representative of the
  // underlying object so the new handle points straight at it. The fresh handle
  // is a distinct object (a different pointer than the one passed in), which is
  // the "may create two distinct handles" latitude the standard grants.
  VpiObject* rep = ResolveSameObject(object);
  auto* handle = AllocObject();
  handle->type = rep->type;

  // §37.2.1: the new handle and the original both refer to the same object, so
  // they are equivalent. Recording that this handle denotes `rep` lets
  // vpi_compare_objects() resolve the two to a common representative and report
  // them equal despite their pointers differing.
  handle->same_object_as = rep;
  return handle;
}

void VpiContext::ReleaseHandle(VpiHandle handle) {
  // §37.2.2: vpi_release_handle() causes the tool to release a handle. Marking
  // the handle released is all that is needed: the underlying object is not
  // touched, so a distinct handle to the same object - held perhaps by another
  // VPI program - is unaffected and can still refer to that object. A null
  // handle names nothing.
  if (!handle) return;
  handle->released = true;
}

PLI_INT32 VpiContext::ReleaseHandleStatus(VpiHandle handle) {
  // §38.38: vpi_release_handle() shall free the memory a VPI routine allocated
  // for a handle. It shall not be called on an invalid handle: a null,
  // already-released, or no-longer-existing handle names no live memory to
  // free, so the call fails and returns 0.
  if (!HandleValid(handle)) return 0;

  // §38.38: an iterator object (from vpi_iterate(), §38.21) carries storage
  // that vpi_scan() reclaims only once a traversal reaches its end. When a
  // program breaks out of an iteration loop before that, vpi_release_handle()
  // frees the iterator's memory. An iterator is allocated standalone - it is
  // not one of the tracked objects - so its storage is returned here directly,
  // the same way vpi_scan() disposes of an exhausted one.
  if (handle->type == vpiIterator) {
    delete handle;
    return 1;
  }

  // §38.38: for any other handle, freeing it is the §37.2.2 release operation -
  // the handle stops being a live handle to its object while the object itself
  // is left in place. The routine succeeds, returning 1.
  ReleaseHandle(handle);
  return 1;
}

bool VpiContext::HandleReleased(VpiHandle handle) const {
  return handle != nullptr && handle->released;
}

bool VpiContext::HandleValid(VpiHandle handle) const {
  // §37.2.4: validity runs from a handle's creation until one of the events
  // that ends it. A null handle names no object and so is never valid. A
  // released handle (§37.2.2) is no longer a live handle to its object, and a
  // handle whose object has ceased to exist (§38.3) no longer refers to a live
  // object; both are invalid. Tool termination, the remaining terminating
  // event, disposes of the context and every handle with it, so a handle that
  // is still queryable here has not hit that case. What is left is a valid
  // handle: non-null, unreleased, and naming an object that still exists.
  if (!handle) return false;
  if (handle->released) return false;
  if (!handle->object_exists) return false;
  return true;
}

bool VpiContext::HandleSurvivesRestart(VpiHandle handle) const {
  // §37.2.2 (restart): a restart releases every handle except those naming a
  // cbStartOfRestart or cbEndOfRestart callback. A surviving handle is
  // therefore a callback handle whose registered reason is one of the two
  // restart reasons.
  if (!handle || handle->type != kVpiCallback) return false;
  if (handle->index < 0 ||
      handle->index >= static_cast<int>(callbacks_.size())) {
    return false;
  }
  int reason = callbacks_[handle->index].reason;
  return reason == kCbStartOfRestart || reason == kCbEndOfRestart;
}

void VpiContext::ReleaseHandlesForRestart() {
  // §37.2.2 (restart): release all handles except the restart-callback handles.
  // Every allocated handle is visited; the two surviving kinds are left live.
  for (VpiObject* handle : all_objects_) {
    if (!HandleSurvivesRestart(handle)) handle->released = true;
  }
}

// §37.2.2: release a handle along with the handles to every callback placed on
// the object it names. A callback handle records, in `index`, the slot of the
// callback whose `obj` is the watched object; any such handle is released too.
void VpiContext::ReleaseHandleWithCallbacks(VpiObject* object) {
  if (!object) return;
  object->released = true;
  for (VpiObject* cb : cb_handles_) {
    if (cb->index >= 0 && cb->index < static_cast<int>(callbacks_.size()) &&
        callbacks_[cb->index].obj == object) {
      cb->released = true;
    }
  }
}

// §37.2.2: release a handle, every subelement reachable through its children,
// and the callbacks placed on any of them. Shared by the frame/thread-free and
// class-reclaim rules; the two differ only in which children they descend into.
void VpiContext::ReleaseHandleSubtree(VpiObject* root) {
  if (!root) return;
  ReleaseHandleWithCallbacks(root);
  for (VpiObject* child : root->children) ReleaseHandleSubtree(child);
}

void VpiContext::ReleaseFrameOrThreadObject(VpiHandle root) {
  // §37.2.2 (frame/thread free): release the freed object, all of its
  // subelements, and the callbacks placed on any of them.
  ReleaseHandleSubtree(root);
}

void VpiContext::ReleaseClassObject(VpiHandle class_object) {
  // §37.2.2 (class reclaim): release the class object and the callbacks on it,
  // then release each automatic data member together with all of its
  // subelements. Non-automatic (static) data members are left live - they are
  // not reclaimed with the class object.
  if (!class_object) return;
  ReleaseHandleWithCallbacks(class_object);
  for (VpiObject* member : class_object->children) {
    if (member->automatic) ReleaseHandleSubtree(member);
  }
}

bool VpiContext::SetDefaultCompatibilityMode(int mode) {
  // §36.12.2.2: only one default mode is selectable for a given simulation run.
  // Once a mode has been selected, refuse any request that would change it so
  // the run keeps a single, consistent default; a request for the mode already
  // in force is consistent and is accepted.
  if (default_compat_mode_selected_ && mode != default_compat_mode_) {
    return false;
  }
  default_compat_mode_ = mode;
  default_compat_mode_selected_ = true;
  return true;
}

int VpiContext::EffectiveCompatibilityMode(bool uses_mechanism1,
                                           int mechanism1_mode) const {
  // §36.12.2.2: the run-wide default determines the compatibility-mode VPI
  // behavior for every application not using the compile-based scheme. An
  // application that does use Mechanism 1 is governed by the mode compiled into
  // it, so the default does not apply to it.
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
  // §37.49: an assertion is registered under one of the assertion-class kinds
  // so a null-referenced iteration over the assertion class (the circle
  // relation) can reach it. An unnamed assertion is not entered in the by-name
  // map.
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
    // §38.35: each element is reachable as a vpiReg over its variable, keyed by
    // its flat ordinal so vpi_put_value_array() can locate it.
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
  // Function-local static: the default context is constructed lazily on first
  // use (catchable) rather than during static init before main.
  static VpiContext default_context;
  if (g_vpi_context) return *g_vpi_context;
  return default_context;
}

void SetGlobalVpiContext(VpiContext* ctx) { g_vpi_context = ctx; }

void InvokeVlogStartupRoutines(VlogStartupRoutine* routines) {
  if (!routines) return;
  // §36.10.2: the routines in the vlog_startup_routines[] array execute in the
  // startup phase, when very little VPI functionality is available. Establish
  // that phase for the duration of the walk so the function-availability
  // restriction is in force while the routines register their system
  // tasks/functions and callbacks, then restore the prior phase afterwards. The
  // array-walking itself is unchanged (that is §36.9.1's mechanism); this only
  // narrows the available functionality for its duration.
  VpiContext& ctx = GetGlobalVpiContext();
  VpiToolPhase prior = ctx.ToolPhase();
  ctx.SetToolPhase(VpiToolPhase::kStartup);
  for (size_t i = 0; routines[i] != nullptr; ++i) {
    routines[i]();
  }
  ctx.SetToolPhase(prior);
}

bool VpiPhaseRestrictsFunctionality(VpiToolPhase phase) {
  // §36.10.2: only the full phase (cbEndOfCompile onward) makes all
  // functionality available; the startup phase and the sizetf phase that
  // follows it - which permits no access beyond the startup phase - both
  // restrict it.
  return phase != VpiToolPhase::kFull;
}

bool VpiRoutineAvailableInStartup(VpiRoutine routine) {
  // §36.10.2: only the two registration routines may be called while the
  // vlog_startup_routines[] array executes.
  return routine == VpiRoutine::kRegisterSystf ||
         routine == VpiRoutine::kRegisterCb;
}

bool VpiStartupCallbackReasonAllowed(int reason) {
  // §36.10.2: the only reasons vpi_register_cb() may be registered for while
  // VPI functionality is restricted.
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
  // §38.36.2: the seven time-related callback reasons. Their placement is
  // constrained through the s_cb_data time structure (see RegisterCb).
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
  // §38.37.1: the name shall begin with a dollar sign and shall be followed by
  // one or more characters legal in a SystemVerilog simple identifier. A null
  // pointer, an empty string, or a bare "$" with nothing after it fails the
  // "one or more" requirement.
  if (tfname == nullptr || tfname[0] != '$' || tfname[1] == '\0') return false;
  for (const char* p = tfname + 1; *p != '\0'; ++p) {
    char c = *p;
    bool legal = (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
                 (c >= '0' && c <= '9') || c == '_' || c == '$';
    if (!legal) return false;
  }
  return true;
}

int VpiSystfReturnType(const VpiSystfData& data) {
  // §38.37.1: sysfunctype shall only be used when type is set to vpiSysFunc, so
  // it names a return-value kind only for a system function; a system task has
  // no return-value kind.
  if (data.type != kVpiSysFunc) return 0;
  return data.sysfunctype;
}

bool VpiSystfCallbackFiresAtBuild(VpiSystfCallback callback) {
  // §38.37.1: callbacks to compiletf and sizetf occur when the simulation data
  // structure is compiled or built; callbacks to calltf occur each time the
  // system task or function is invoked during simulation execution.
  return callback == VpiSystfCallback::kCompiletf ||
         callback == VpiSystfCallback::kSizetf;
}

int VpiSystfInvoke(int (*routine)(const char*), void* user_data) {
  // §38.37.1: the only argument passed to a compiletf/sizetf/calltf routine is
  // the user_data field, typed as PLI_BYTE8 * (char *). One or more of the
  // routine fields may be null when not needed, so a null pointer is skipped.
  if (routine == nullptr) return 0;
  return routine(static_cast<const char*>(user_data));
}

bool VpiSystfSizetfIsCalled(const VpiSystfData& data) {
  // §38.37.1: the sizetf application shall only be called if the type is
  // vpiSysFunc and the sysfunctype is vpiSizedFunc or vpiSizedSignedFunc.
  return data.type == kVpiSysFunc && (data.sysfunctype == kVpiSizedFunc ||
                                      data.sysfunctype == kVpiSizedSignedFunc);
}

int VpiSystfResultSizeBits(const VpiSystfData& data) {
  // §38.37.1: a sized system function takes its width from the sizetf
  // application when one is provided; with no sizetf it returns 32 bits.
  if (VpiSystfSizetfIsCalled(data) && data.sizetf != nullptr) {
    return VpiSystfInvoke(data.sizetf, data.user_data);
  }
  return kVpiDefaultSizedFuncBits;
}

// §H.13 time bridge for the DPI C layer (declared in dpi.h). Each accessor
// reads the design-wide time state through the global VPI context, so the DPI
// svGetTime/svGetTimeUnit/svGetTimePrecision functions deliver the very values
// VPI's vpi_get_time()/vpi_get(vpiTimeUnit/vpiTimePrecision) deliver for a null
// object. The VPI time constants are used here, inside the VPI translation
// unit, keeping them out of svdpi.cpp where they would clash with svdpi.h's
// spelling.
void DpiGetSimTime(bool want_scaled_real, uint32_t* high, uint32_t* low,
                   double* real) {
  VpiTime t = {};
  // GetTime selects the result form from t.type: a scaled real, or the raw
  // 64-bit simulation-time count. A null object means "the whole design", which
  // GetTime reads in the simulation time unit.
  t.type = want_scaled_real ? kVpiScaledRealTime : kVpiSimTime;
  GetGlobalVpiContext().GetTime(nullptr, &t);
  if (high) *high = t.high;
  if (low) *low = t.low;
  if (real) *real = t.real;
}

int32_t DpiGetSimTimeUnit() {
  return static_cast<int32_t>(GetGlobalVpiContext().Get(vpiTimeUnit, nullptr));
}

int32_t DpiGetSimTimePrecision() {
  return static_cast<int32_t>(
      GetGlobalVpiContext().Get(vpiTimePrecision, nullptr));
}

}  // namespace delta
