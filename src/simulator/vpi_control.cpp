#include <cctype>
#include <cmath>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <optional>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/dpi.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"
#include "simulator/vpi_coverage.h"
#include "simulator/vpi_model_helpers1.h"
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

}  // namespace

std::string CoverageScopeName(const VpiObject* scope_handle) {
  if (scope_handle == nullptr || (!VpiIsInstanceType(scope_handle->type) &&
                                  !VpiIsAssertionType(scope_handle->type))) {
    return std::string();
  }
  if (!scope_handle->full_name.empty()) return scope_handle->full_name;
  return std::string(scope_handle->name);
}

// §40.5.1's coverage type properties name the same four coverage types §40.3.1
// names with its `SV_COV_* macros, and §40.5.3 has the VPI operations carry the
// semantics of the system functions that take those macros. One coverage of one
// type, then, whichever door it is reached through - so a property arriving
// through VPI is put into the terms the coverage state is keyed in before it
// reaches the state. Untranslated, a database saved by $coverage_save under
// `SV_COV_ASSERTION held nothing a vpi_control(vpiCoverageMerge,
// vpiAssertCoverage, ...) could find, and a database saved through VPI was as
// invisible to $coverage_merge, each reporting `SV_COV_NOCOV over coverage the
// other had just recorded.
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

// §40.5.3: statement, toggle, and FSM coverage are not individually
// controllable, so the Start/Stop/Reset/Check actions act on the scope the
// handle names as a whole rather than on any per-statement, per-signal, or
// per-FSM object. The return is the §40.3.1 status value the equivalent system
// function produces, so the detailed outcome -- and the collection-state change
// it reflects -- is observable to the caller.
CoverageControlState& VpiContext::GetCoverageControlState() {
  // §40.2: "This clause defines the coverage API in SystemVerilog" - one API,
  // of which §40.5's routines are the VPI extension rather than a second one,
  // and §40.5.3's controls "carry the semantics of $coverage_control()". So
  // what a PLI application starts, stops, resets or reads is the coverage of
  // the run it is loaded into: the state the SimContext keeps, which the
  // language's own access functions of §40.3.2 answer out of. Two stores would
  // have meant a design whose $coverage_get reported nothing of what a PLI
  // application had been collecting, and the reverse.
  //
  // A context with no run attached - a PLI application reaching the routines
  // before a design is there, and a test that stands a VpiContext up alone -
  // has this context's own state to work in instead.
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
      // §40.5.3: Start/Stop/Reset/Check control the collection of coverage over
      // a scope, with the semantics of $coverage_control() (§40.3.2.1). The
      // coverage type selects the kind of coverage being controlled but, since
      // statement, toggle, and FSM coverage are not individually controllable,
      // the control acts on the instance (or assertion) the handle names as a
      // whole rather than on any sub-object of it.
      CoverageControl control = CoverageControlForOperation(operation);
      std::string scope = CoverageScopeName(scope_handle);
      return static_cast<int>(
          GetCoverageControlState().Control(control, scope));
    }
    case vpiCoverageSave:
      // §40.5.3: save the current coverage of the requested type to the named
      // coverage database, per $coverage_save() (§40.3.2.5). The type is the
      // one §40.3.1 names, so the entry is one $coverage_merge can load.
      return static_cast<int>(GetCoverageControlState().CoverageSave(
          CoverageTypeForVpiProperty(coverage_type).value_or(coverage_type),
          name));
    case vpiCoverageMerge:
      // §40.5.3: merge coverage of the requested type from the named coverage
      // database into the simulation, per $coverage_merge() (§40.3.2.4), and
      // in the same terms, so a database $coverage_save wrote is found here.
      return static_cast<int>(GetCoverageControlState().CoverageMerge(
          CoverageTypeForVpiProperty(coverage_type).value_or(coverage_type),
          name));
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

namespace {

// §38.17: the option this tool passes a file of options with. The driver reads
// it in src/driver/cli_options.cpp, and the clause says what
// vpi_get_vlog_info() reports of such a file: "the argument strings returned by
// vpi_get_vlog_info() shall contain the vendor option string name followed by a
// pointer to a NULL-terminated array of pointers to characters".
constexpr std::string_view kVpiVendorOptionsFileFlag = "-f";

// The driver caps how deep options files may nest; this walk caps it the same
// way, so a file that names its way back to itself ends here too.
constexpr int kVpiMaxOptionsFileDepth = 16;

// §38.17: one array of pointers the report holds - the command line itself, or
// the parsed contents of an options file. An entry is either a word, given as
// its index in the string pool, or the pointer to a nested array, given as that
// array's index.
struct VpiArgvEntry {
  size_t word = 0;
  int nested_array = -1;
};
struct VpiArgvArray {
  std::vector<VpiArgvEntry> entries;
  size_t offset = 0;
};

// §38.17: the words an options file holds, parsed the way the tool parses them
// - whitespace-separated, a word beginning with # commenting out the rest of
// its line.
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

// §38.17: lay one list of words into an array of the report, pooling each word
// and opening a nested array wherever the vendor option names a file. Returns
// the index of the array it built.
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
    // §38.17: "The value in entry zero shall contain the name of the file. The
    // remaining entries shall contain pointers to NULL-terminated character
    // arrays containing the different options in the file."
    std::vector<std::string> nested = {words[i + 1]};
    for (std::string& word : VpiOptionsFileWords(words[i + 1])) {
      nested.push_back(std::move(word));
    }
    int child = VpiBuildArgvArray(nested, depth + 1, pool, arrays);
    (*arrays)[static_cast<size_t>(self)].entries.push_back({0, child});
    ++i;  // the file name is the nested array's entry zero, not an entry here
  }
  return self;
}

// §38.17: give every array a place in the report and fill in the words. The
// command line comes first and its entries are argc; each array after it ends
// in the NULL the clause requires, so it is one longer than its entries. The
// pointer a vendor file option is followed by is left for VpiLinkArgvArrays,
// which needs every array's place before it can name one.
void VpiPlaceArgvArrays(const std::vector<std::string>& pool,
                        std::vector<VpiArgvArray>* arrays,
                        std::vector<const char*>* argv) {
  size_t offset = 0;
  for (size_t k = 0; k < arrays->size(); ++k) {
    (*arrays)[k].offset = offset;
    offset += (*arrays)[k].entries.size() + (k == 0 ? 0 : 1);
  }
  argv->assign(offset, nullptr);
  for (const VpiArgvArray& array : *arrays) {
    size_t at = array.offset;
    for (const VpiArgvEntry& entry : array.entries) {
      if (entry.nested_array < 0) (*argv)[at] = pool[entry.word].c_str();
      ++at;
    }
  }
}

// §38.17: "the vendor option string name followed by a pointer to a
// NULL-terminated array of pointers to characters" - the pointer is written
// here, once the array it reaches has a place of its own in the report.
void VpiLinkArgvArrays(const std::vector<VpiArgvArray>& arrays,
                       std::vector<const char*>* argv) {
  for (const VpiArgvArray& array : arrays) {
    size_t at = array.offset;
    for (const VpiArgvEntry& entry : array.entries) {
      if (entry.nested_array >= 0) {
        const char** nested =
            argv->data() +
            arrays[static_cast<size_t>(entry.nested_array)].offset;
        (*argv)[at] = reinterpret_cast<const char*>(nested);
      }
      ++at;
    }
  }
}

}  // namespace

bool VpiContext::GetVlogInfo(VpiVlogInfo* info) {
  // §38.17: a null result structure cannot receive the information, so the
  // routine fails.
  if (!info) return false;

  // §38.17: rebuild the report. The command line is the first array and its
  // length is argc, entry zero being the tool name - both guaranteed by how
  // invocation_args_ was populated. Wherever it names an options file, the
  // entry after the vendor option holds a pointer to that file's own array
  // rather than the file name as a string, and those arrays are laid out after
  // the command line's entries. Nothing built them: a named file was reported
  // as the plain word it was written as, so what the tool had actually read out
  // of it was in the report nowhere.
  invocation_file_args_.clear();
  std::vector<VpiArgvArray> arrays;
  VpiBuildArgvArray(invocation_args_, 0, &invocation_file_args_, &arrays);
  VpiPlaceArgvArrays(invocation_file_args_, &arrays, &invocation_argv_);
  VpiLinkArgvArrays(arrays, &invocation_argv_);

  info->argc = static_cast<int>(arrays.empty() ? 0 : arrays[0].entries.size());
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
// describe a valid intermodule path, so it is rejected by the caller, which is
// also where a missing reference has already been answered.
bool InterModPathSizeMismatch(int type, VpiHandle ref1, VpiHandle ref2) {
  return type == vpiInterModPath && ref1->size != ref2->size;
}

// Whether `obj` is one of the objects `ref` reaches.
bool IsChildOf(VpiHandle ref, const VpiObject* obj) {
  for (auto* child : ref->children) {
    if (child == obj) return true;
  }
  return false;
}

// §38.22 Synopsis: "Obtain a handle for an object in a many-to-one
// relationship." The one object is the one of kind `type` that every reference
// object reaches: an object only one of them reaches stands in a relationship
// with that one alone, which is the one-to-one relationship vpi_handle() is
// for. §37.37 detail 1 is this rule read for an intermodule path -- "To get to
// an intermodule path, vpi_handle_multi(vpiInterModPath, port1, port2) can be
// used" -- whose one object is the path running between the two named ports.
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

// §38.22 Returns: "vpiHandle -- Handle to an object." What comes back is the
// object of the many-to-one relationship rather than anything holding it, which
// is what the Related routines row separates this routine from its neighbours
// by: vpi_iterate() and vpi_scan() walk a one-to-many relationship and
// vpi_handle() answers a one-to-one one. So an application that reaches an
// intermodule path this way holds the path itself and can put delays on it.
VpiHandle VpiContext::HandleMulti(int type, VpiHandle ref1, VpiHandle ref2) {
  if (!ref1 || !ref2) return nullptr;

  if (InterModPathSizeMismatch(type, ref1, ref2)) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_handle_multi(): the two ports of an intermodule path must be of "
        "the same size";
    return nullptr;
  }

  return ObjectSharedBy(ref1, ref2, type);
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
  if (a == b) return 1;

  // §38.3 asks whether the handles "refer to the same underlying simulation
  // object", and for a variable or a net that object is the storage the run
  // keeps for it - which two objects of the model can name at once, a net and
  // the variable its resolution writes among them. Only the representatives
  // were compared, so two handles on one piece of the run's storage answered
  // that they were different objects.
  if (a->var != nullptr && a->var == b->var) return 1;
  return a->net != nullptr && a->net == b->net ? 1 : 0;
}

VpiHandle VpiContext::CreateHandleFor(VpiHandle object) {
  // §37.2.1: a null object denotes nothing, so there is no handle to create.
  if (object == nullptr) return nullptr;

  // Resolve through any existing alias chain to the representative of the
  // underlying object so the new handle points straight at it. The fresh handle
  // is a distinct object (a different pointer than the one passed in), which is
  // the "may create two distinct handles" latitude the standard grants.
  VpiObject* rep = ResolveSameObject(object);

  // §37.2.4: "A tool can create a handle that refers to an object only during
  // the lifetime of the object." Past that lifetime there is no object for a
  // handle to refer to, so none is made; a handle handed back here would be
  // invalid from the moment it was created, and §37.2.4 forbids a program both
  // from referring through it and from releasing it.
  if (!rep->object_exists) return nullptr;

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

  // Existence is a property of the object, while release is a property of the
  // handle. A handle made by CreateHandleFor() is a record of its own that
  // aliases the representative, so its own object_exists flag says nothing
  // about the object it denotes: the chain has to be resolved first, or an
  // alias to an object that has ceased to exist answers that it is still valid.
  return ResolveSameObject(handle)->object_exists;
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
//
// §37.2.3: which callbacks those are is settled by §38.3's comparison rather
// than by a C "==" of the handles, since a callback is placed on an object and
// the application may have registered it through a handle other than the one
// being released.
void VpiContext::ReleaseHandleWithCallbacks(VpiObject* object) {
  if (!object) return;
  object->released = true;
  for (VpiObject* cb : cb_handles_) {
    if (cb->index >= 0 && cb->index < static_cast<int>(callbacks_.size()) &&
        CompareObjects(callbacks_[cb->index].obj, object) != 0) {
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

  // §37.3.8: "The life of a transient object may be tracked through various
  // callbacks", and a frame and a thread are two of the kinds it names. The end
  // of one is where cbEndOfFrame and cbEndOfThread are delivered; an
  // application that registered either was called by nothing at all, so the
  // life it was registered to track ran its course unreported.
  if (root == nullptr) return;
  if (root->type == vpiFrame) DispatchCallbacks(cbEndOfFrame, root);
  if (root->type == vpiThread) DispatchCallbacks(cbEndOfThread, root);
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

  // §37.3.8: reclaiming the memory of a class object is the end of that
  // object's life, and the subclause gives it two of the callbacks it lists -
  // cbReclaimObj for the reclaim itself and cbEndOfObject for the object
  // ceasing to exist. Neither was delivered from anywhere.
  DispatchCallbacks(cbReclaimObj, class_object);
  DispatchCallbacks(cbEndOfObject, class_object);
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

bool VpiContext::RoutineIsUnavailableNow(VpiRoutine routine) {
  // §36.10.2 restricts by phase and then by routine: the two registration
  // routines are available throughout, and everything else waits for the full
  // phase.
  if (!VpiPhaseRestrictsFunctionality(tool_phase_)) return false;
  if (VpiRoutineAvailableInStartup(routine)) return false;
  last_error_.state = kVpiPLI;
  last_error_.level = kVpiError;
  last_error_.message =
      "VPI routine is not available until cbEndOfCompile; only "
      "vpi_register_systf() and vpi_register_cb() may be called before then";
  return true;
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

int VpiContext::SystfResultSizeBits(const VpiSystfData& data) {
  // The registration this record is, if it is one of ours. Compared by address
  // rather than by content: two registrations may carry identical fields, and
  // §36.8.1 counts sizetf calls per registration.
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
