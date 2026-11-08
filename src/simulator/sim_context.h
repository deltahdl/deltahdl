#pragma once

#include <cstdint>
#include <cstdio>
#include <functional>
#include <memory>
#include <optional>
#include <ostream>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_stmt.h"
#include "simulator/assert_control_log.h"
#include "simulator/class_object.h"
#include "simulator/clocking.h"
#include "simulator/cover_results.h"
#include "simulator/coverage.h"
#include "simulator/coverage_control.h"
#include "simulator/covergroup_instance.h"
#include "simulator/dpi_runtime.h"
#include "simulator/file_monitor.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/net.h"
#include "simulator/output_log.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context_file_tables.h"
#include "simulator/sim_context_name_tables.h"
#include "simulator/sim_context_random_stability.h"
#include "simulator/sim_context_scope_stack.h"
#include "simulator/sim_context_type_ref_compares.h"
#include "simulator/sim_context_types.h"
#include "simulator/specify.h"
#include "simulator/sva_engine_sampling.h"
#include "simulator/sync_objects.h"
#include "simulator/unit_scopes.h"
#include "simulator/variable.h"
#include "simulator/vcd_dump_state.h"
#include "simulator/vcd_writer.h"

namespace delta {

class DiagEngine;
class SpecifyManager;
struct DataType;
struct ModuleItem;
struct Process;
struct Stmt;

class SimContext : public DeclaredNameTables,
                   public RandomStability,
                   public ScopeStack,
                   public TypeRefCompares {
 public:
  SimContext(Scheduler& sched, Arena& arena, DiagEngine& diag,
             uint32_t seed = 0)
      : scheduler_(sched), arena_(arena), diag_(diag), default_seed_(seed) {
    scheduler_.SetContext(this);
    running_unit_scope_ = [this] { return ActiveUnitScope(); };
  }

  ~SimContext();

  Variable* FindVariable(std::string_view name);
  Variable* FindInGenerateBlock(const std::string& inst_prefix,
                                std::string_view name);

  Variable* CreateVariable(std::string_view name, uint32_t width);

  void AliasVariable(std::string_view alias_name, std::string_view target_name);
  void AliasVariable(std::string_view alias_name, Variable* target);
  void NullifyEventVariable(std::string_view name);

  Net* FindNet(std::string_view name);
  Net* CreateNet(std::string_view name, NetType type, uint32_t width,
                 const NetSpec& spec = {});

  void AliasNet(std::string_view alias_name, std::string_view target_name);

  Scheduler& GetScheduler() { return scheduler_; }
  Arena& GetArena() { return arena_; }
  DiagEngine& GetDiag() { return diag_; }
  SimTime CurrentTime() const { return scheduler_.CurrentTime(); }

  void RequestStop() { stop_requested_ = true; }
  bool StopRequested() const { return stop_requested_; }

  void RequestFinish();
  bool FinishRequested() const { return finish_requested_; }
  void NoteRuntimeError() { ++runtime_error_count_; }
  bool HasRuntimeErrors() const { return runtime_error_count_ > 0; }

  void SetInteractiveScope(std::string_view name);
  const std::string& InteractiveScope() const { return interactive_scope_; }
  void RegisterHierarchicalScope(std::string_view name);
  bool IsHierarchicalScope(std::string_view name) const;

  void RecordListing(std::string_view name);
  const std::string& LastListedScope() const { return last_listed_scope_; }

  std::vector<std::string> HierarchicalScopesUnder(std::string_view scope,
                                                   bool recursive) const;
  void RecordShowScopes(std::string_view scope, bool recursive);
  const std::string& LastShownScope() const { return last_shown_scope_; }
  bool ShowScopesRecursive() const { return show_scopes_recursive_; }

  void RegisterScopeVariables(std::string_view scope, ScopeVariableSet set);
  const ScopeVariableSet* ScopeVariables(std::string_view scope) const;
  void RecordShowVars(std::string_view scope, std::vector<std::string> vars);
  const std::string& LastShowVarsScope() const { return last_showvars_scope_; }
  const std::vector<std::string>& ShowVarsVariables() const;

  std::ostream& Out() { return log_.Out(); }
  OutputLog& Log() { return log_; }
  bool LoggingEnabled() const { return log_.Enabled(); }
  const std::string& LogFile() const { return log_.Name(); }

  CoverageControlState& GetCoverageControlState() { return coverage_control_; }

  void RegisterProgramInitial(uint32_t program_block_id, Process* proc);
  void OnProgramInitialComplete(Process* proc);
  void ExitProgramBlock(uint32_t program_block_id);
  bool ProgramsEnded() const { return programs_ended_; }

  void SetDelayMode(DelayMode mode) { delay_mode_ = mode; }
  DelayMode GetDelayMode() const { return delay_mode_; }

  void SetGlobalPrecision(TimeUnit u);
  TimeUnit GlobalPrecision() const { return global_precision_; }
  TimeUnit StepTimeUnit() const { return global_precision_; }

  const TimeFormatSpec& GetTimeFormat() const { return time_format_; }
  void SetTimeFormat(const TimeFormatSpec& spec);

  void SetCurrentTimeScale(const TimeScale& ts) { current_timescale_ = ts; }
  const TimeScale& CurrentTimeScale() const { return current_timescale_; }

  void SetCurrentScopeName(std::string_view name);
  const std::string& CurrentScopeName() const { return current_scope_name_; }

  void SetCompUnitTimeScale(const TimeScale& ts) { compunit_timescale_ = ts; }
  const TimeScale& CompUnitTimeScale() const { return compunit_timescale_; }

  void SetScopeTimeScale(std::string_view name, const TimeScale& ts);
  const TimeScale* FindScopeTimeScale(std::string_view name) const;

  void RegisterFinalProcess(Process* proc);
  void RunFinalBlocks();

  const ModuleItem* EnterSubroutinePackage(const ModuleItem* func);
  void PushStaticScope(std::string_view func_name);
  void PopStaticScope(std::string_view func_name);
  std::string_view StaticFrameKey(std::string_view name);

  Logic4Vec* SetRsReturnSlot(Logic4Vec* slot);
  Logic4Vec* RsReturnSlot() const { return rs_return_slot_; }

  std::vector<std::string> PackageFrameKeys(std::string_view name) const;
  std::vector<std::string> ScopedObjectKeys(std::string_view name) const;
  Variable* FindInPackageScope(std::string_view name);
  ModuleItem* FindFunctionInPackageScope(std::string_view name);
  bool IsUnitPathFromRoot(std::string_view name);
  Variable* FindUnitPathVariable(std::string_view name);
  Variable* CreateLocalVariable(std::string_view name, uint32_t width,
                                bool is_signed = false);

  Variable* FindStaticFuncVar(std::string_view func_name,
                              std::string_view var_name);

  void SaveStaticFuncVar(std::string_view func_name, std::string_view var_name,
                         Variable* var);

  void EnterFunction() { ++function_depth_; }
  void ExitFunction();
  bool InFunction() const { return function_depth_ > 0; }

  void PushQueueRefFrame();
  void RecordQueueRef(const QueueRefBinding& binding);
  std::vector<QueueRefBinding> PopQueueRefFrame();

  void PushAssocRefFrame();
  void RecordAssocRef(const AssocRefBinding& binding);
  std::vector<AssocRefBinding> PopAssocRefFrame();

  VcdDumpState& Vcd() { return vcd_; }
  const VcdDumpState& Vcd() const { return vcd_; }

  VcdWriter* OpenVcdDump(std::string_view top_scope, bool wait_for_dumpvars,
                         VcdFileType type);
  VcdWriter* OpenVcdDumpFromTask(VcdFileType type);
  void CloseVcdDump();
  void CloseDumpportsDump();

  void SetSpecifyManager(SpecifyManager* mgr) { specify_manager_ = mgr; }
  SpecifyManager* GetSpecifyManager() { return specify_manager_; }
  SpecifyManager& AcquireSpecifyManager();

  void RegisterVcdSignals(VcdWriter& vcd);
  void RegisterVcdPackageSignals(VcdWriter& vcd);
  void RegisterVcdSignalsOf(VcdWriter& vcd, bool packages);
  bool IsVcdPackageVariable(std::string_view name) const;
  bool IsUndumpableVcdName(std::string_view name) const;

  void SetDpiRuntime(DpiRuntime* dpi);
  DpiRuntime* GetDpiRuntime() { return dpi_runtime_; }

  DpiRuntime& AcquireDpiRuntime();

  void SetCurrentProcess(Process* proc);
  Process* CurrentProcess() const { return current_process_; }
  bool IsReactiveContext() const;

  void SetLoweringInstancePrefix(std::string_view prefix);

  std::string ActiveInstancePrefix() const;
  std::string_view ActiveGenBlockPrefix() const;
  UnitScopes& Units() { return units_; }
  std::string ActiveUnitScope() const;
  static std::string_view GenBlockPrefixOf(const Process& proc);
  std::optional<bool> TypeRefCompareHere(const Expr* expr) const;

  InstancePrefixOverrideState& InstancePrefixOverride() {
    return prefix_override_;
  }

  void SetDisableTarget(std::string_view name) { disable_target_ = name; }
  std::string_view GetDisableTarget() const { return disable_target_; }
  void ClearDisableTarget() { disable_target_ = {}; }

  void RegisterNamedScope(std::string_view name, Process* proc);
  void UnregisterNamedScope(std::string_view name, Process* proc);
  const std::vector<Process*>& FindNamedScopeProcesses(
      std::string_view name) const;

  void RegisterOutermostScope(std::string_view name, Process* proc);
  const std::vector<Process*>& FindOutermostScopeProcesses(
      std::string_view name) const;

  void PushActiveNamedScope(std::string_view name);
  void PopActiveNamedScope() { active_scope_stack_.pop_back(); }
  const std::vector<std::string_view>& ActiveNamedScopes() const;

  void AddPendingViolation(SourceLoc loc, std::string msg, Subclause subclause,
                           CaseQualifier qual = CaseQualifier::kUnique);
  void FlushPendingViolations();
  void MaturePendingViolations();

  void FlushPendingDeferredReports();

  uint64_t CurrentDeferredReportGeneration() const;

  const std::unordered_map<std::string_view, Variable*>& GetVariables() const {
    return variables_;
  }

  const std::unordered_map<std::string_view, Net*>& GetNets() const {
    return nets_;
  }

  std::unordered_map<uint64_t, StochasticQueue>& StochasticQueues() {
    return stochastic_queues_;
  }

  uint32_t Urandom32();
  void SeedUrandom(uint32_t seed);
  uint32_t UrandomRange(uint32_t min_val, uint32_t max_val);

  std::mt19937& ActiveRng();

  uint32_t DrawSeedForChild();

  void RegisterArray(std::string_view name, const ArrayInfo& info);

  void RegisterLocalArray(std::string_view name, const ArrayInfo& info);

  void RegisterArrayInScope(std::string_view name, const ArrayInfo& info);

  void RegisterStringVariable(std::string_view name);
  bool IsStringVariable(std::string_view name);
  ArrayInfo* FindArrayInfo(std::string_view name);
  const ArrayInfo* FindArrayInfo(std::string_view name) const;

  QueueObject* CreateQueue(std::string_view name, uint32_t elem_width,
                           int32_t max_size = -1, bool is_4state = true);
  QueueObject* FindQueue(std::string_view name);
  void AliasQueue(std::string_view alias_name, std::string_view target_name);

  AssocArrayObject* CreateAssocArray(std::string_view name, uint32_t elem_width,
                                     bool is_string_key,
                                     const AssocArraySpec& spec = {});
  AssocArrayObject* FindAssocArray(std::string_view name);
  void AliasAssocArray(std::string_view alias_name,
                       std::string_view target_name);

  void SetVariableTag(std::string_view var_name, std::string_view tag);
  std::string_view GetVariableTag(std::string_view var_name) const;

  void RegisterInstanceBinding(std::string_view prefix,
                               std::string_view library, std::string_view cell);
  std::string_view FindInstanceBinding(std::string_view prefix) const;

  void SetDeferredBindingScope(std::optional<std::string> prefix);
  const std::optional<std::string>& DeferredBindingScope() const;

  std::string ResolveInstanceScope(std::string_view ident) const;

  void AddPlusArg(std::string arg);
  const std::vector<std::string>& GetPlusArgs() const { return plus_args_; }

  static constexpr uint32_t kFdMsb = 0x80000000u;
  static constexpr uint32_t kStdinFd = 0x80000000u;
  static constexpr uint32_t kStdoutFd = 0x80000001u;
  static constexpr uint32_t kStderrFd = 0x80000002u;

  uint32_t OpenFile(std::string_view filename, std::string_view mode);
  uint32_t OpenMcd(std::string_view filename);
  void CloseFile(uint32_t descriptor);
  FILE* GetFileHandle(uint32_t fd);
  bool IsFdReadable(uint32_t fd) const;
  std::vector<FILE*> GetMcdFiles(uint32_t mcd);

  void SetFileIoError(uint32_t fd, int32_t code, std::string msg);
  void ClearFileIoError(uint32_t fd);
  const FileIoError* GetFileIoError(uint32_t fd) const;

  void SetFdEofDetected(uint32_t fd, bool detected);
  bool FdEofDetected(uint32_t fd) const;
  std::string& FdPushback(uint32_t fd) { return files_.pushback[fd]; }
  std::vector<std::unique_ptr<FileMonitor>>& FileMonitors() {
    return files_.monitors;
  }
  SimFileTables& FileTables() { return files_; }
  std::unordered_map<std::string, std::function<void(char)>>&
  UdpStateSetters() {
    return udp_state_setters_;
  }

  SemaphoreObject* CreateSemaphore(std::string_view name, int32_t keys);
  SemaphoreObject* FindSemaphore(std::string_view name);
  SemaphoreObject** SemaphoreSlot(std::string_view name);
  MailboxObject** MailboxSlot(std::string_view name);
  void AliasSemaphore(std::string_view alias_name,
                      std::string_view target_name);

  MailboxObject* CreateMailbox(std::string_view name, int32_t bound);
  MailboxObject* FindMailbox(std::string_view name);
  void AliasMailbox(std::string_view alias_name, std::string_view target_name);

  void SetEventTriggered(std::string_view name);
  bool IsEventTriggered(std::string_view name) const;

  void RegisterClassType(std::string_view name, ClassTypeInfo* info);
  ClassTypeInfo* FindClassType(std::string_view name) const;
  std::string SetClassInstanceScope(std::string scope);
  const std::string& ClassInstanceScope() const { return class_scope_; }
  ClassTypeInfo* ExactClassType(std::string_view name);
  std::vector<ClassTypeInfo*> RegisteredClassTypes(bool all = false) const;
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
  ClassObject* ConstraintCallerThis() const { return constraint_caller_this_; }
  ClassObject* SetConstraintCallerThis(ClassObject* obj);
  ClassObject* CurrentThis() const;
  void CopyCarriedStacksTo(Process& child) const;
  uint64_t CurrentThisHandle() const;

  void NotifyClassHandleWatchers(uint64_t handle);

  void PushMethodClass(const ClassTypeInfo* cls);
  void PopMethodClass();
  const ClassTypeInfo* CurrentMethodClass() const;

  void IncrementAssertionFailCount() { ++assertion_fail_count_; }
  int AssertionFailCount() const { return assertion_fail_count_; }

  ImmediateCoverResults& ImmediateCovers() { return immediate_covers_; }
  ConcurrentCoverResults& ConcurrentCovers() { return concurrent_covers_; }

  AssertControlLog& AssertControls() { return assert_controls_; }

  void SetLastSeverity(std::string_view sev, std::string_view msg, SimTime t,
                       std::string_view scope = {}, uint32_t line = 0);
  std::string_view LastSeverity() const { return last_severity_; }
  std::string_view LastSeverityMsg() const { return last_severity_msg_; }
  SimTime LastSeverityTime() const { return last_severity_time_; }
  std::string_view LastSeverityScope() const { return last_severity_scope_; }
  uint32_t LastSeverityLine() const { return last_severity_line_; }

  void SetClockingManager(class ClockingManager* mgr) { clocking_mgr_ = mgr; }
  class ClockingManager* GetClockingManager() { return clocking_mgr_; }
  ClockingManager& AcquireClockingManager();

  void SetCoverageDB(class CoverageDB* db) { coverage_db_ = db; }
  class CoverageDB* GetCoverageDB() { return coverage_db_; }
  class CoverageDB& CoverageData();
  CovergroupTable& Covergroups();

  void SetDeferredArgSnapshot(const Expr* arg, const Logic4Vec& val);
  const Logic4Vec* FindDeferredArgSnapshot(const Expr* arg) const;
  void ClearDeferredArgSnapshot(const Expr* arg);

  AssertionSampleStore& AssertionSamples() { return assertion_samples_; }

  std::unordered_map<const Expr*, Expr*>& ParenFreeCalls() {
    return paren_free_calls_;
  }
  std::unordered_map<const Stmt*, const Stmt*>& ClassTypedefShapedDecls() {
    return class_typedef_shaped_decls_;
  }

  void SetActiveMonitor(const Expr* call);
  const Expr* ActiveMonitor() const { return active_monitor_; }

  void SetMonitorCaller(std::shared_ptr<Process> caller);
  Process* MonitorCaller() const { return monitor_caller_.get(); }
  uint64_t MonitorGeneration() const { return monitor_generation_; }

  void SetMonitorEnabled(bool on) { monitor_enabled_ = on; }
  bool MonitorEnabled() const { return monitor_enabled_; }

  bool MonitorDisplayPending() const { return monitor_display_pending_; }
  void SetMonitorDisplayPending(bool pending);

  const Logic4Vec* MonitorLastValue(Variable* var) const;
  void SetMonitorLastValue(Variable* var, const Logic4Vec& value);

 private:
  std::string InstanceKeyOf(const std::string& cand) const;
  Scheduler& scheduler_;
  Arena& arena_;
  DiagEngine& diag_;
  uint32_t default_seed_;
  std::unordered_map<std::string_view, Variable*> variables_;
  std::unordered_map<std::string_view, Net*> nets_;
  Logic4Vec* rs_return_slot_ = nullptr;

  std::vector<Process*> final_processes_;
  void RecordVcdTimestep(VcdWriter* writer);
  void CloseOneVcdDump(VcdDump& dump);
  VcdDumpState vcd_;
  SpecifyManager* specify_manager_ = nullptr;
  std::unique_ptr<SpecifyManager> owned_specify_manager_;
  std::unique_ptr<DpiRuntime> owned_dpi_runtime_;
  DpiRuntime* dpi_runtime_ = nullptr;
  Process* current_process_ = nullptr;
  std::string lowering_inst_prefix_;
  UnitScopes units_;
  InstancePrefixOverrideState prefix_override_;
  bool stop_requested_ = false;
  bool finish_requested_ = false;
  uint32_t runtime_error_count_ = 0;
  std::string interactive_scope_;
  std::unordered_set<std::string> hierarchical_scopes_;
  std::string last_listed_scope_;
  std::string last_shown_scope_;
  bool show_scopes_recursive_ = false;
  std::unordered_map<std::string, ScopeVariableSet> scope_variables_;
  std::string last_showvars_scope_;
  std::vector<std::string> showvars_variables_;
  OutputLog log_;
  CoverageControlState coverage_control_;

  std::unordered_map<const Expr*, Logic4Vec> deferred_arg_snapshots_;

  AssertionSampleStore assertion_samples_;
  std::unordered_map<const Expr*, Expr*> paren_free_calls_;
  std::unordered_map<const Stmt*, const Stmt*> class_typedef_shaped_decls_;

  const Expr* active_monitor_ = nullptr;
  std::shared_ptr<Process> monitor_caller_;
  uint64_t monitor_generation_ = 0;
  bool monitor_enabled_ = true;
  bool monitor_display_pending_ = false;
  std::unordered_map<Variable*, Logic4Vec> monitor_last_values_;

  uint32_t pending_program_initials_ = 0;
  bool programs_ended_ = false;

  std::unordered_map<uint32_t, std::vector<Process*>>
      program_initials_by_block_;
  DelayMode delay_mode_ = DelayMode::kTyp;
  TimeUnit global_precision_ = TimeUnit::kNs;
  TimeFormatSpec time_format_;
  bool time_format_explicit_ = false;
  TimeScale current_timescale_;
  std::string current_scope_name_;
  TimeScale compunit_timescale_;
  std::unordered_map<std::string, TimeScale> scope_timescales_;
  std::vector<std::string> plus_args_;
  SimFileTables files_;
  std::unordered_map<std::string, std::function<void(char)>> udp_state_setters_;
  void EnsureStdioDescriptors();

  std::unordered_map<std::string_view, ArrayInfo> array_infos_;
  std::unordered_map<uint64_t, StochasticQueue> stochastic_queues_;
  std::unordered_map<std::string_view, QueueObject*> queues_;
  std::unordered_map<std::string_view, AssocArrayObject*> assoc_arrays_;
  std::unordered_map<std::string_view, std::string> var_tags_;
  std::unordered_map<std::string_view, SemaphoreObject*> semaphores_;
  std::unordered_map<std::string_view, MailboxObject*> mailboxes_;
  std::unordered_map<std::string_view, uint64_t> event_triggered_;
  std::unordered_map<std::string_view, ClassTypeInfo*> class_types_;
  std::string class_scope_;
  bool instance_classes_ = false;
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
  ClassObject* constraint_caller_this_ = nullptr;
  std::vector<const ClassTypeInfo*> method_class_stack_;
  std::vector<std::vector<QueueRefBinding>> queue_ref_stack_;
  std::vector<std::vector<AssocRefBinding>> assoc_ref_stack_;

  std::unordered_map<std::string, std::string> instance_bindings_;
  std::optional<std::string> deferred_binding_scope_;

  int assertion_fail_count_ = 0;
  ImmediateCoverResults immediate_covers_;
  ConcurrentCoverResults concurrent_covers_;

  AssertControlLog assert_controls_;

  std::string last_severity_;
  std::string last_severity_msg_;
  SimTime last_severity_time_{};
  std::string last_severity_scope_;
  uint32_t last_severity_line_ = 0;

  class ClockingManager* clocking_mgr_ = nullptr;
  std::unique_ptr<ClockingManager> owned_clocking_manager_;
  class CoverageDB* coverage_db_ = nullptr;
  std::unique_ptr<class CoverageDB> owned_coverage_db_;
  std::unique_ptr<CovergroupTable> covergroups_;
  std::string_view disable_target_;
  std::unordered_map<std::string, std::vector<Process*>> named_scope_map_;
  std::unordered_map<std::string, std::vector<Process*>> outermost_scope_map_;
  static const std::vector<Process*> kEmptyNamedScopeList;
  std::vector<std::string_view> active_scope_stack_;
};

}  // namespace delta
