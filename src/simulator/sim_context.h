#pragma once

#include <array>
#include <cstdint>
#include <cstdio>
#include <deque>
#include <map>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/coverage_control.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sync_objects.h"
#include "simulator/variable.h"

namespace delta {

class DiagEngine;
class DpiContext;
class VcdWriter;
struct ModuleItem;
struct Process;

struct EnumMemberInfo {
  std::string_view name;
  uint64_t value = 0;
};

struct EnumTypeInfo {
  std::string_view type_name;
  std::vector<EnumMemberInfo> members;
};

struct StructFieldInfo {
  std::string_view name;
  uint32_t bit_offset = 0;
  uint32_t width = 0;
  DataTypeKind type_kind = DataTypeKind::kLogic;
};

struct StructTypeInfo {
  std::string_view type_name;
  std::vector<StructFieldInfo> fields;
  uint32_t total_width = 0;
  bool is_packed = false;
  bool is_union = false;
  bool is_soft = false;
};

struct QueueObject {
  std::vector<Logic4Vec> elements;
  std::vector<uint64_t> element_ids;
  uint32_t elem_width = 32;
  // Whether the element type is 4-state. Fixes the value yielded when an
  // element of the queue is absent (Table 7-1, see 7.4.5): x for 4-state
  // element types, 0 for 2-state ones.
  bool is_4state = true;
  int32_t max_size = -1;
  uint32_t generation = 0;

  uint64_t AllocateId() { return ++next_elem_id_; }

  void AssignFreshIds();

 private:
  uint64_t next_elem_id_ = 0;
};

struct QueueRefBinding {
  QueueObject* queue = nullptr;
  uint64_t element_id = 0;
  Variable* local_var = nullptr;
};

struct AssocArrayObject;

struct AssocRefBinding {
  AssocArrayObject* assoc = nullptr;
  bool is_string_key = false;
  int64_t int_key = 0;
  std::string str_key;
  Variable* local_var = nullptr;
};

struct AssocArrayObject {
  std::map<int64_t, Logic4Vec> int_data;
  std::map<std::string, Logic4Vec> str_data;
  uint32_t elem_width = 32;
  uint32_t index_width = 32;
  bool is_string_key = false;
  bool is_wildcard = false;
  bool is_4state = false;
  // Signedness of an integral index type: controls whether an index expression
  // is sign- or zero-extended to the index width before becoming a key, which
  // in turn fixes the iteration ordering (§7.8.4).
  bool is_index_signed = true;
  bool has_default = false;
  Logic4Vec default_value;
  uint32_t Size() const;
};

struct ArrayInfo {
  uint32_t lo = 0;
  uint32_t size = 0;
  uint32_t elem_width = 32;
  bool is_descending = false;
  bool is_dynamic = false;
  bool is_queue = false;
  bool is_4state = true;
  DataTypeKind elem_type_kind = DataTypeKind::kImplicit;
  // §21.4.3: address extents of each unpacked dimension, outermost (leftmost in
  // the declaration) first, for a multidimensional unpacked array. Empty when
  // the array has a single unpacked dimension, in which case lo/size above
  // describe it. $readmemb/$readmemh consult these to fill the array in
  // row-major order and to resolve an @-address against the highest dimension.
  std::vector<uint32_t> dim_los;
  std::vector<uint32_t> dim_sizes;
};

// §20.15.3: a queued entry as the queue manager retains it. $q_add records the
// job_id and the user-defined inform_id; $q_remove hands both back through its
// output arguments when the entry is taken off the queue. §20.15.5 additionally
// stamps each entry with the simulation time it was placed, so the queue's
// wait-time statistics can be derived when an entry leaves or is examined.
struct StochasticQueueEntry {
  uint64_t job_id = 0;
  uint64_t inform_id = 0;
  uint64_t arrival_tick = 0;
};

// §20.15: per-queue bookkeeping for the stochastic-analysis queue tasks.
// The queue type and capacity validated at creation and the running occupancy
// drive the §20.15.6 status codes (the full and empty conditions of Table
// 20-11). `entries` holds the stored entries in arrival order so that
// §20.15.3 $q_remove can return the job_id/inform_id of the entry it removes,
// selected per the FIFO/LIFO discipline fixed by the q_type (see §20.15.1).
//
// The remaining fields accumulate the activity statistics that §20.15.5
// $q_exam reports through Table 20-10: the peak occupancy ever reached, the
// span and number of arrivals (for the mean interarrival time), and the
// completed-wait totals (count, sum and minimum) gathered as entries are
// removed.
struct StochasticQueue {
  int64_t q_type = 0;
  int64_t max_length = 0;
  uint64_t count = 0;
  std::deque<StochasticQueueEntry> entries;

  uint64_t max_count = 0;
  uint64_t arrivals = 0;
  uint64_t first_arrival_tick = 0;
  uint64_t last_arrival_tick = 0;
  uint64_t departures = 0;
  uint64_t total_wait = 0;
  uint64_t shortest_wait = 0;
};

enum class DelayMode : uint8_t { kMin, kTyp, kMax };

// State block governed by $timeformat (see 20.4.3). The four members map
// 1:1 to the task's arguments and persist between invocations.
struct TimeFormatSpec {
  int units_number = -9;
  int precision_number = 0;
  std::string suffix_string;
  int minimum_field_width = 20;
};

class SimContext {
 public:
  SimContext(Scheduler& sched, Arena& arena, DiagEngine& diag,
             uint32_t seed = 0);

  Variable* FindVariable(std::string_view name);
  Variable* CreateVariable(std::string_view name, uint32_t width);

  void AliasVariable(std::string_view alias_name, std::string_view target_name);

  void NullifyEventVariable(std::string_view name);

  Net* FindNet(std::string_view name);
  Net* CreateNet(std::string_view name, NetType type, uint32_t width,
                 Strength charge_strength = Strength::kMedium,
                 uint64_t decay_ticks = 0, bool is_user_nettype = false,
                 std::string_view resolve_func = {}, bool is_signed = false);

  Scheduler& GetScheduler() { return scheduler_; }
  Arena& GetArena() { return arena_; }
  DiagEngine& GetDiag() { return diag_; }
  SimTime CurrentTime() const { return scheduler_.CurrentTime(); }

  void RequestStop() { stop_requested_ = true; }
  bool StopRequested() const { return stop_requested_; }

  // Optional $reset family (Annex D.8). RecordReset tallies one reset of the
  // tool and remembers the reset_value argument so that the $reset_value
  // system function can hand that value back after the reset. $reset_count
  // reports how many resets have occurred.
  void RecordReset(int64_t reset_value) {
    ++reset_count_;
    reset_value_ = reset_value;
  }
  uint32_t ResetCount() const { return reset_count_; }
  int64_t ResetValue() const { return reset_value_; }

  // Optional $scope system task (Annex D.11). The interactive scope names the
  // level of hierarchy used when identifying objects interactively. Its initial
  // setting is the first top-level module (established at lowering); a $scope
  // call retargets it to the complete hierarchical name supplied as its single
  // argument (a module, task, function, or named block). This mirrors, on the
  // system-task side, the interactive scope that vpi_control reaches through
  // vpiSetInteractiveScope (§38.4).
  void SetInteractiveScope(std::string_view name) {
    interactive_scope_ = std::string(name);
  }
  const std::string& InteractiveScope() const { return interactive_scope_; }

  // §40.3.2.1 coverage-collection state driven by $coverage_control.
  CoverageControlState& GetCoverageControlState() { return coverage_control_; }

  void RegisterProgramInitial(uint32_t program_block_id, Process* proc);
  void OnProgramInitialComplete(Process* proc);

  void ExitProgramBlock(uint32_t program_block_id);

  void SetDelayMode(DelayMode mode) { delay_mode_ = mode; }
  DelayMode GetDelayMode() const { return delay_mode_; }

  void SetGlobalPrecision(TimeUnit u) {
    global_precision_ = u;
    if (!time_format_explicit_) {
      time_format_.units_number = static_cast<int>(u);
    }
  }
  TimeUnit GlobalPrecision() const { return global_precision_; }
  TimeUnit StepTimeUnit() const { return global_precision_; }

  // $timeformat state per 20.4.3. The defaults follow Table 20-3; the unit
  // number tracks the global precision until $timeformat is invoked.
  const TimeFormatSpec& GetTimeFormat() const { return time_format_; }
  void SetTimeFormat(const TimeFormatSpec& spec) {
    time_format_ = spec;
    time_format_explicit_ = true;
  }

  // Timescale of the design element that is the current scope, reported by
  // $timeunit/$timeprecision when no argument is supplied (see 20.4.1).
  void SetCurrentTimeScale(const TimeScale& ts) { current_timescale_ = ts; }
  const TimeScale& CurrentTimeScale() const { return current_timescale_; }

  // Name of the design element that is the current scope. $printtimescale with
  // no argument prints this name in its report line (see 20.4.2).
  void SetCurrentScopeName(std::string_view name) {
    current_scope_name_ = std::string(name);
  }
  const std::string& CurrentScopeName() const { return current_scope_name_; }

  // Timescale of the compilation unit, reported when the $unit argument is
  // passed to $timeunit/$timeprecision.
  void SetCompUnitTimeScale(const TimeScale& ts) { compunit_timescale_ = ts; }
  const TimeScale& CompUnitTimeScale() const { return compunit_timescale_; }

  // Timescale of a named design element, reported when that element is passed
  // as the argument to $timeunit/$timeprecision.
  void SetScopeTimeScale(std::string_view name, const TimeScale& ts) {
    scope_timescales_[std::string(name)] = ts;
  }
  const TimeScale* FindScopeTimeScale(std::string_view name) const {
    auto it = scope_timescales_.find(std::string(name));
    return it == scope_timescales_.end() ? nullptr : &it->second;
  }

  void RegisterFinalProcess(Process* proc);
  void RunFinalBlocks();

  void AddSensitivity(std::string_view signal, Process* proc);
  const std::vector<Process*>& GetSensitiveProcesses(
      std::string_view signal) const;

  void RegisterFunction(std::string_view name, ModuleItem* item);
  ModuleItem* FindFunction(std::string_view name);

  void RegisterLetDecl(std::string_view name, ModuleItem* item);
  ModuleItem* FindLetDecl(std::string_view name);

  void RegisterSequenceDecl(std::string_view name, ModuleItem* item);
  ModuleItem* FindSequenceDecl(std::string_view name);

  void PushScope();
  void PopScope();

  // §18.17.7: while a randsequence production with a non-void return type is
  // being generated, the engine points the return slot at the production's
  // return-value storage. A 'return <expr>' executed anywhere in that
  // production's code blocks evaluates its expression into this slot. The slot
  // is null outside randsequence value generation, so an ordinary procedural
  // return is unaffected. The setter returns the previous slot so nested
  // production generation can save and restore it.
  Logic4Vec* SetRsReturnSlot(Logic4Vec* slot) {
    Logic4Vec* prev = rs_return_slot_;
    rs_return_slot_ = slot;
    return prev;
  }
  Logic4Vec* RsReturnSlot() const { return rs_return_slot_; }

  std::vector<std::unordered_map<std::string_view, Variable*>> SwapScopeStack(
      std::vector<std::unordered_map<std::string_view, Variable*>> new_stack);
  void PushStaticScope(std::string_view func_name);
  void PopStaticScope(std::string_view func_name);
  bool HasLocalScope() const { return !scope_stack_.empty(); }
  Variable* FindLocalVariable(std::string_view name);
  Variable* CreateLocalVariable(std::string_view name, uint32_t width);

  Variable* FindStaticFuncVar(std::string_view func_name,
                              std::string_view var_name);

  void SaveStaticFuncVar(std::string_view func_name, std::string_view var_name,
                         Variable* var);

  void AliasLocalVariable(std::string_view name, Variable* var);

  void PushFuncName(std::string_view name);
  void PopFuncName();
  std::string_view CurrentFuncName() const;
  // The active subroutine call chain, outermost frame first. Used to report the
  // call stack for $stacktrace (§20.17.2).
  const std::vector<std::string_view>& FuncNameStack() const {
    return func_name_stack_;
  }

  void EnterFunction() { ++function_depth_; }
  void ExitFunction() { if (function_depth_ > 0) --function_depth_; }
  bool InFunction() const { return function_depth_ > 0; }

  void PushQueueRefFrame();
  void RecordQueueRef(const QueueRefBinding& binding);
  std::vector<QueueRefBinding> PopQueueRefFrame();

  void PushAssocRefFrame();
  void RecordAssocRef(const AssocRefBinding& binding);
  std::vector<AssocRefBinding> PopAssocRefFrame();

  void SetVcdWriter(VcdWriter* vcd) { vcd_writer_ = vcd; }
  VcdWriter* GetVcdWriter() { return vcd_writer_; }

  void SetDumpFileName(std::string name) { dump_file_name_ = std::move(name); }
  const std::string& GetDumpFileName() const { return dump_file_name_; }

  // §21.7.3.1: scope names supplied to $dumpports must be unique across every
  // call. Records the scope and returns false when it repeats one already used
  // by an earlier $dumpports call.
  bool RegisterDumpportsScope(const std::string& scope) {
    return dumpports_scopes_.insert(scope).second;
  }
  // §21.7.3.1: an explicitly named $dumpports output file may not be named by
  // more than one call. Records the name and returns false on a repeat.
  bool RegisterDumpportsFile(const std::string& file) {
    return dumpports_files_.insert(file).second;
  }
  // §21.7.3.7: an extended VCD control task may name the $dumpports output it
  // targets; the name matches only when some $dumpports call explicitly
  // specified that file. Returns true when the name was so registered.
  bool IsDumpportsFile(const std::string& file) const {
    return dumpports_files_.count(file) != 0;
  }
  // §21.7.3.7: true once at least one $dumpports call has explicitly named an
  // output file, so a control task's filename can be matched against the set.
  bool HasDumpportsFiles() const { return !dumpports_files_.empty(); }

  void SetDpiContext(DpiContext* dpi) { dpi_context_ = dpi; }
  DpiContext* GetDpiContext() { return dpi_context_; }

  void SetCurrentProcess(Process* proc) { current_process_ = proc; }
  Process* CurrentProcess() const { return current_process_; }
  bool IsReactiveContext() const;

  void SetDisableTarget(std::string_view name) { disable_target_ = name; }
  std::string_view GetDisableTarget() const { return disable_target_; }
  void ClearDisableTarget() { disable_target_ = {}; }

  void RegisterNamedScope(std::string_view name, Process* proc);
  void UnregisterNamedScope(std::string_view name, Process* proc);
  const std::vector<Process*>& FindNamedScopeProcesses(
      std::string_view name) const;

  void PushActiveNamedScope(std::string_view name) {
    active_scope_stack_.push_back(name);
  }
  void PopActiveNamedScope() { active_scope_stack_.pop_back(); }
  const std::vector<std::string_view>& ActiveNamedScopes() const {
    return active_scope_stack_;
  }

  void AddPendingViolation(std::string msg);
  void FlushPendingViolations();
  void MaturePendingViolations();

  const std::unordered_map<std::string_view, Variable*>& GetVariables() const {
    return variables_;
  }

  // §20.15.6: the live registry of stochastic-analysis queues, keyed by the
  // q_id supplied to $q_initialize. Its membership drives the "undefined
  // q_id" status, and each entry's capacity and occupancy drive the "queue
  // full" and "queue empty" statuses.
  std::unordered_map<uint64_t, StochasticQueue>& StochasticQueues() {
    return stochastic_queues_;
  }

  int32_t Random32();
  uint32_t Urandom32();
  // Reseed the generator so a given seed always replays the same sequence.
  void SeedUrandom(uint32_t seed);
  uint32_t UrandomRange(uint32_t min_val, uint32_t max_val);

  // Returns the mt19937 stream that the running thread must draw from.
  // Falls back to the context-wide generator when no thread is current.
  std::mt19937& ActiveRng();

  // Pulls the next value from the active stream, the seed material a freshly
  // created child thread inherits per §18.14.2 hierarchical seeding.
  uint32_t DrawSeedForChild();

  // §18.14.3 object stability: hand back the generator that belongs solely to
  // this instance. Because every object draws from its own stream, the
  // randomization of one instance is independent of any other instance and of
  // the $random/$urandom and per-thread generators. The stream is materialized
  // lazily from the seed installed at allocation (§18.14.1), so the draw
  // sequence stays reproducible.
  std::mt19937& ObjectRng(ClassObject* obj);

  // §18.14.3: an instance can be reseeded at any time via srandom(), letting an
  // object self-seed (typically inside its new method) so its randomization
  // replays under the chosen seed.
  void SeedObjectRng(ClassObject* obj, uint32_t seed);

  // §18.13.4 get_randstate(): hand back the object's current RNG internal state
  // as a string. mt19937 fully serializes its state through operator<<, so the
  // returned value captures the complete generator state -- not merely the
  // seed -- and reading it does not advance the stream. The string's length and
  // contents are implementation dependent.
  std::string GetRandState(ClassObject* obj);

  // §18.13.4 get_randstate(): the same retrieval for the RNG owned by a process
  // (the state obtained via the process's get_randstate() method).
  std::string GetRandState(Process* proc);

  // §18.13.5 set_randstate(): install `state` as the object's RNG internal
  // state, the inverse of GetRandState. mt19937 round-trips its full state
  // through operator>>, so a value previously produced by GetRandState restores
  // the generator to the exact stream position it was read from. The stream is
  // marked live so a later draw does not reseed over the restored state. The
  // value is treated as an opaque string of implementation-dependent length and
  // format; supplying one not obtained from GetRandState is undefined.
  void SetRandState(ClassObject* obj, const std::string& state);

  // §18.13.5 set_randstate(): the same install for the RNG owned by a process
  // (the state given to the process's set_randstate() method).
  void SetRandState(Process* proc, const std::string& state);

  void RegisterRealVariable(std::string_view name);
  bool IsRealVariable(std::string_view name) const;

  void RegisterStringVariable(std::string_view name);
  bool IsStringVariable(std::string_view name) const;

  void RegisterUnboundedParam(std::string_view name);
  bool IsUnboundedParam(std::string_view name) const;

  void RegisterEnumType(std::string_view name, const EnumTypeInfo& info);
  const EnumTypeInfo* FindEnumType(std::string_view name) const;
  void SetVariableEnumType(std::string_view var_name,
                           std::string_view type_name);
  const EnumTypeInfo* GetVariableEnumType(std::string_view var_name) const;

  void RegisterStructType(std::string_view name, const StructTypeInfo& info);
  const StructTypeInfo* FindStructType(std::string_view name) const;
  void SetVariableStructType(std::string_view var_name,
                             std::string_view type_name);
  const StructTypeInfo* GetVariableStructType(std::string_view var_name) const;

  void RegisterArray(std::string_view name, const ArrayInfo& info);
  ArrayInfo* FindArrayInfo(std::string_view name);
  const ArrayInfo* FindArrayInfo(std::string_view name) const;

  QueueObject* CreateQueue(std::string_view name, uint32_t elem_width,
                           int32_t max_size = -1, bool is_4state = true);
  QueueObject* FindQueue(std::string_view name);

  AssocArrayObject* CreateAssocArray(std::string_view name, uint32_t elem_width,
                                     bool is_string_key,
                                     uint32_t index_width = 32,
                                     bool is_wildcard = false,
                                     bool is_4state = false,
                                     bool is_index_signed = true);
  AssocArrayObject* FindAssocArray(std::string_view name);

  void SetVariableTag(std::string_view var_name, std::string_view tag);
  std::string_view GetVariableTag(std::string_view var_name) const;

  void RegisterTypeWidth(std::string_view name, uint32_t width);
  uint32_t FindTypeWidth(std::string_view name) const;

  void RegisterInstanceType(std::string_view prefix, std::string_view type);
  std::string_view FindInstanceType(std::string_view prefix) const;

  // §33.7: record the resolved "library.cell" binding of a module instance,
  // keyed by the same instance-path prefix used for instance types. The %l/%L
  // display format specifier reports this for the instance that contains the
  // running display task, mirroring how %m reports that instance's hierarchical
  // path name. An unrecorded prefix has no binding and reads back empty.
  void RegisterInstanceBinding(std::string_view prefix,
                               std::string_view library, std::string_view cell);
  std::string_view FindInstanceBinding(std::string_view prefix) const;

  // §25.9 virtual interface runtime. A virtual interface variable carries a
  // binding to the scope of the interface instance it currently refers to, or
  // is unbound (the null state, which is also the value before initialization).
  // Bindings are keyed by the variable object, so no name re-resolution is
  // needed when the binding is later consulted.
  void RegisterVirtualInterfaceVar(const Variable* v);
  bool IsVirtualInterfaceVar(const Variable* v) const;
  void BindVirtualInterface(const Variable* v, std::string_view scope);
  void UnbindVirtualInterface(const Variable* v);
  bool VirtualInterfaceIsBound(const Variable* v) const;
  std::string_view VirtualInterfaceBinding(const Variable* v) const;
  // Full hierarchical scope of an interface instance named `ident` relative to
  // the current process, or empty if `ident` is not a known interface instance.
  std::string ResolveInstanceScope(std::string_view ident) const;

  void AddPlusArg(std::string arg);
  const std::vector<std::string>& GetPlusArgs() const { return plus_args_; }

  // Per §21.3.1: when type is supplied, $fopen yields a 32-bit fd whose MSB is
  // set; when type is omitted, $fopen yields a 32-bit mcd whose MSB is clear
  // and a single channel bit (1..30) is set. STDIN/STDOUT/STDERR have reserved
  // fd values 32'h8000_0000/0001/0002.
  static constexpr uint32_t kFdMsb = 0x80000000u;
  static constexpr uint32_t kStdinFd = 0x80000000u;
  static constexpr uint32_t kStdoutFd = 0x80000001u;
  static constexpr uint32_t kStderrFd = 0x80000002u;

  uint32_t OpenFile(std::string_view filename, std::string_view mode);
  uint32_t OpenMcd(std::string_view filename);
  void CloseFile(uint32_t descriptor);
  FILE* GetFileHandle(uint32_t fd);
  // §21.3.4: a file descriptor may be read from only when it was opened with a
  // read or read-update type ("r" or "r+"); the pre-opened STDIN channel is
  // also readable. Write/append descriptors report false.
  bool IsFdReadable(uint32_t fd) const;
  std::vector<FILE*> GetMcdFiles(uint32_t mcd);

  SemaphoreObject* CreateSemaphore(std::string_view name, int32_t keys);
  SemaphoreObject* FindSemaphore(std::string_view name);

  MailboxObject* CreateMailbox(std::string_view name, int32_t bound);
  MailboxObject* FindMailbox(std::string_view name);

  void SetEventTriggered(std::string_view name);
  bool IsEventTriggered(std::string_view name) const;

  void RegisterClassType(std::string_view name, ClassTypeInfo* info);
  ClassTypeInfo* FindClassType(std::string_view name);
  void SetVariableClassType(std::string_view var, std::string_view type);
  std::string_view GetVariableClassType(std::string_view var) const;
  void SetVariableClassParamExprs(std::string_view var,
                                  std::vector<Expr*> exprs);
  const std::vector<Expr*>& GetVariableClassParamExprs(
      std::string_view var) const;

  uint64_t AllocateClassObject(ClassObject* obj);
  ClassObject* GetClassObject(uint64_t handle) const;
  void DeallocateClassObject(uint64_t handle);

  void RetainObject(uint64_t handle);
  void ReleaseObject(uint64_t handle);

  Reachability GetReachability(uint64_t handle) const;

  void CollectGarbage();

  void RegisterWeakReference(WeakReference* wr);
  void UnregisterWeakReference(WeakReference* wr);

  uint64_t AllocateWeakReference(uint64_t referent_handle, Arena& arena);
  WeakReference* FindWeakReferenceByHandle(uint64_t handle) const;

  uint64_t RegisterProcessHandle(Process* proc);
  Process* FindProcessByHandle(uint64_t handle) const;

  void PushThis(ClassObject* obj);
  void PopThis();
  ClassObject* CurrentThis() const;

  void IncrementAssertionFailCount() { ++assertion_fail_count_; }
  int AssertionFailCount() const { return assertion_fail_count_; }

  void IncrementCoverEvalCount() { ++cover_eval_count_; }
  void IncrementCoverSuccessCount() { ++cover_success_count_; }
  int CoverEvalCount() const { return cover_eval_count_; }
  int CoverSuccessCount() const { return cover_success_count_; }

  void SetLastSeverity(std::string_view sev, std::string_view msg, SimTime t) {
    last_severity_ = std::string(sev);
    last_severity_msg_ = std::string(msg);
    last_severity_time_ = t;
  }
  std::string_view LastSeverity() const { return last_severity_; }
  std::string_view LastSeverityMsg() const { return last_severity_msg_; }
  SimTime LastSeverityTime() const { return last_severity_time_; }

  void SetClockingManager(class ClockingManager* mgr) { clocking_mgr_ = mgr; }
  class ClockingManager* GetClockingManager() { return clocking_mgr_; }

  void SetCoverageDB(class CoverageDB* db) { coverage_db_ = db; }
  class CoverageDB* GetCoverageDB() { return coverage_db_; }

  void SetDeferredArgSnapshot(const Expr* arg, const Logic4Vec& val) {
    deferred_arg_snapshots_[arg] = val;
  }
  const Logic4Vec* FindDeferredArgSnapshot(const Expr* arg) const {
    auto it = deferred_arg_snapshots_.find(arg);
    if (it == deferred_arg_snapshots_.end()) return nullptr;
    return &it->second;
  }
  void ClearDeferredArgSnapshot(const Expr* arg) {
    deferred_arg_snapshots_.erase(arg);
  }

  // §21.2.3 continuous monitoring. Only one $monitor display list can be
  // active at a time; recording a new one bumps the generation so that
  // watchers left behind by a superseded list deactivate themselves.
  void SetActiveMonitor(const Expr* call) {
    active_monitor_ = call;
    ++monitor_generation_;
  }
  const Expr* ActiveMonitor() const { return active_monitor_; }
  uint64_t MonitorGeneration() const { return monitor_generation_; }

  // The monitor flag is toggled by $monitoron/$monitoroff and is on by
  // default at the start of simulation.
  void SetMonitorEnabled(bool on) { monitor_enabled_ = on; }
  bool MonitorEnabled() const { return monitor_enabled_; }

  // At most one monitor display is produced per time step even when several
  // watched signals change together; this flag coalesces them.
  bool MonitorDisplayPending() const { return monitor_display_pending_; }
  void SetMonitorDisplayPending(bool pending) {
    monitor_display_pending_ = pending;
  }

  // The value a watched signal held when its change was last observed, so a
  // write that does not alter the value is not treated as a change.
  const Logic4Vec* MonitorLastValue(Variable* var) const {
    auto it = monitor_last_values_.find(var);
    return it == monitor_last_values_.end() ? nullptr : &it->second;
  }
  void SetMonitorLastValue(Variable* var, const Logic4Vec& value) {
    monitor_last_values_[var] = value;
  }

 private:
  // §13.3.2: static-task (and named-block) storage is per module instance.
  // Qualify the bare scope name with the current process's instance path so
  // that distinct instances of the same module do not share storage. Returns
  // the bare name unchanged at the top level (empty instance prefix).
  std::string_view StaticFrameKey(std::string_view name);

  Scheduler& scheduler_;
  Arena& arena_;
  DiagEngine& diag_;
  std::mt19937 rng_;
  std::unordered_map<std::string_view, Variable*> variables_;
  std::unordered_map<std::string_view, Net*> nets_;
  std::unordered_map<std::string_view, ModuleItem*> functions_;
  std::unordered_map<std::string_view, ModuleItem*> let_decls_;
  std::unordered_map<std::string_view, ModuleItem*> sequence_decls_;
  std::vector<std::unordered_map<std::string_view, Variable*>> scope_stack_;
  Logic4Vec* rs_return_slot_ = nullptr;

  std::unordered_map<std::string_view,
                     std::unordered_map<std::string_view, Variable*>>
      static_frames_;

  std::vector<std::string_view> func_name_stack_;
  std::vector<Process*> final_processes_;
  std::unordered_map<std::string, std::vector<Process*>> sensitivity_map_;
  static const std::vector<Process*> kEmptyProcessList;
  VcdWriter* vcd_writer_ = nullptr;
  std::string dump_file_name_ = "dump.vcd";
  // §21.7.3.1 cross-call $dumpports bookkeeping: scope names and explicitly
  // specified file names must each be unique across all $dumpports calls.
  std::unordered_set<std::string> dumpports_scopes_;
  std::unordered_set<std::string> dumpports_files_;
  DpiContext* dpi_context_ = nullptr;
  Process* current_process_ = nullptr;
  bool stop_requested_ = false;
  uint32_t reset_count_ = 0;
  int64_t reset_value_ = 0;
  std::string interactive_scope_;
  CoverageControlState coverage_control_;

  std::unordered_map<const Expr*, Logic4Vec> deferred_arg_snapshots_;

  const Expr* active_monitor_ = nullptr;
  uint64_t monitor_generation_ = 0;
  bool monitor_enabled_ = true;
  bool monitor_display_pending_ = false;
  std::unordered_map<Variable*, Logic4Vec> monitor_last_values_;

  uint32_t pending_program_initials_ = 0;

  std::unordered_map<uint32_t, std::vector<Process*>> program_initials_by_block_;
  DelayMode delay_mode_ = DelayMode::kTyp;
  TimeUnit global_precision_ = TimeUnit::kNs;
  TimeFormatSpec time_format_;
  bool time_format_explicit_ = false;
  TimeScale current_timescale_;
  std::string current_scope_name_;
  TimeScale compunit_timescale_;
  std::unordered_map<std::string, TimeScale> scope_timescales_;
  std::vector<std::string> plus_args_;
  std::unordered_map<uint32_t, FILE*> file_descriptors_;
  // §21.3.4: descriptors whose open type permits reading ("r"/"r+" families).
  std::unordered_set<uint32_t> readable_fds_;
  // Bit i in mcd_channels_[i] tracks the file opened on channel i (1..30).
  std::array<FILE*, 31> mcd_channels_ = {};
  bool stdio_descriptors_ready_ = false;
  void EnsureStdioDescriptors();

  std::unordered_set<std::string_view> real_vars_;

  std::unordered_set<std::string_view> string_vars_;

  std::unordered_set<std::string_view> unbounded_params_;

  std::unordered_map<std::string_view, EnumTypeInfo> enum_types_;
  std::unordered_map<std::string_view, std::string_view> var_enum_types_;

  std::unordered_map<std::string_view, StructTypeInfo> struct_types_;
  std::unordered_map<std::string_view, std::string_view> var_struct_types_;

  std::unordered_map<std::string_view, ArrayInfo> array_infos_;

  std::unordered_map<std::string_view, QueueObject*> queues_;
  std::unordered_map<uint64_t, StochasticQueue> stochastic_queues_;

  std::unordered_map<std::string_view, AssocArrayObject*> assoc_arrays_;

  std::unordered_map<std::string_view, std::string> var_tags_;

  std::unordered_map<std::string_view, SemaphoreObject*> semaphores_;

  std::unordered_map<std::string_view, MailboxObject*> mailboxes_;

  std::unordered_map<std::string_view, uint64_t> event_triggered_;

  std::unordered_map<std::string_view, ClassTypeInfo*> class_types_;
  std::unordered_map<std::string_view, std::string_view> var_class_types_;
  std::unordered_map<std::string_view, std::vector<Expr*>>
      var_class_param_exprs_;

  std::unordered_map<uint64_t, ClassObject*> class_objects_;
  uint64_t next_handle_id_ = 1;

  std::unordered_set<WeakReference*> weak_references_;

  std::unordered_map<uint64_t, WeakReference*> weak_ref_by_handle_;

  std::unordered_map<uint64_t, Process*> process_handles_;
  uint64_t next_process_handle_id_ = 1;

  int function_depth_ = 0;

  std::vector<ClassObject*> this_stack_;

  std::vector<std::vector<QueueRefBinding>> queue_ref_stack_;
  std::vector<std::vector<AssocRefBinding>> assoc_ref_stack_;

  std::unordered_map<std::string_view, uint32_t> type_widths_;

  std::unordered_map<std::string, std::string> instance_types_;

  // §33.7: per-instance resolved "library.cell" binding strings, keyed like
  // instance_types_ by instance-path prefix; read back by the %l/%L format
  // specifier when it displays the binding of the containing module instance.
  std::unordered_map<std::string, std::string> instance_bindings_;

  // §25.9: virtual interface variables and their current interface-instance
  // scope bindings (absence of a binding means null / uninitialized).
  std::unordered_set<const Variable*> vi_vars_;
  std::unordered_map<const Variable*, std::string> vi_bindings_;

  int assertion_fail_count_ = 0;

  int cover_eval_count_ = 0;
  int cover_success_count_ = 0;

  std::string last_severity_;
  std::string last_severity_msg_;
  SimTime last_severity_time_{};

  class ClockingManager* clocking_mgr_ = nullptr;

  class CoverageDB* coverage_db_ = nullptr;

  std::string_view disable_target_;

  std::unordered_map<std::string, std::vector<Process*>> named_scope_map_;
  static const std::vector<Process*> kEmptyNamedScopeList;

  std::vector<std::string_view> active_scope_stack_;
};

}
