#pragma once

#include <cstddef>
#include <cstdint>
#include <deque>
#include <iosfwd>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/types.h"
#include "simulator/coverage_control.h"
#include "simulator/vpi_channel_state.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_control_requests.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"
#include "simulator/vpi_value_pools.h"

namespace delta {

struct Expr;
struct Process;
struct RtlirDesign;
struct RtlirImport;
struct ModuleItem;
struct TimingCheckEntry;
struct Variable;

class VpiContext {
 public:
  VpiContext() = default;
  ~VpiContext();
  void Attach(SimContext& sim_ctx, const RtlirDesign* design = nullptr);
  SimContext* Run() const { return sim_ctx_; }

  void AttachDesignPorts(const RtlirDesign* design);
  void AttachDesignInterModPaths(const RtlirDesign* design);
  void PlaceSdfDelayDevice(std::string_view source, std::string_view load);
  void AttachTopModules(const RtlirDesign* design);

  void SetScheduler(Scheduler* sched) { scheduler_ = sched; }

  VpiHandle RegisterSystf(s_vpi_systf_data* data);

  bool CallRegisteredSystf(const char* name, const Expr* call_site,
                           SimContext& ctx, Logic4Vec& result, Arena& arena);

  void CallCompiletfForSourceCall(const s_vpi_systf_data& data,
                                  const Expr* call_site, SimContext& ctx,
                                  Arena& arena);

  const s_vpi_systf_data* ResolveSystf(const char* name) const;

  void GetSystfInfo(VpiHandle obj, s_vpi_systf_data* systf_data_p);

  void GetCbInfo(VpiHandle obj, s_cb_data* cb_data_p);

  void GetTime(VpiHandle obj, s_vpi_time* time_p);

  void GetDelays(VpiHandle obj, s_vpi_delay* delay_p);

  void PutDelays(VpiHandle obj, s_vpi_delay* delay_p);

  int GetData(int id, char* data_loc, int num_of_bytes);

  void SeedSaveData(int id, const char* data, int len);

  int PutData(int id, const char* data_loc, int num_of_bytes);

  int PutUserData(VpiHandle obj, void* userdata);

  void* GetUserData(VpiHandle obj);

  void ClearUserDataForRestartOrReset();

  void SetSimTimeUnit(int exponent) { sim_time_unit_ = exponent; }
  int SimTimeUnit() const { return sim_time_unit_; }

  VpiHandle CreateTimeQueue();

  void SetTimeQueueSlots(std::vector<VpiTimeQueueSlot> slots) {
    time_queue_slots_ = std::move(slots);
  }

  VpiHandle HandleByName(const char* name, VpiHandle scope);
  VpiHandle HandleByIndex(int index, VpiHandle parent);

  VpiHandle HandleByMultiIndex(int num_index, const int* index_array,
                               VpiHandle parent);
  VpiHandle Handle(int type, VpiHandle ref);
  VpiHandle Iterate(int type, VpiHandle ref, int compatibility_mode = 0);
  VpiHandle Scan(VpiHandle iterator);
  void GetValue(VpiHandle obj, s_vpi_value* value);
  VpiHandle PutValue(VpiHandle obj, s_vpi_value* value, s_vpi_time* time,
                     int flags);
  VpiHandle RegisterCb(s_cb_data* data);
  int RemoveCb(VpiHandle cb_handle);
  int ExecuteCallback(VpiHandle cb_handle);
  void RegisterCbValueChange(const s_cb_data& data);

  int DispatchCallbacks(int reason, VpiHandle obj = nullptr,
                        void* user_data = nullptr);
  int DeliverCallback(VpiHandle cb_handle);
  int DeliverRaisedSignals();
  int DispatchStrengthChange(VpiObject* obj);
  void NoteStmtExecuting(const Stmt* stmt, std::string prefix);
  void NoteThreadCreated(Process* proc);
  void NoteThreadEnded(Process* proc);
  void NoteThreadEntered(Process* proc);
  void NoteTimingViolation(const TimingCheckEntry& check);
  void NoteObjectCreated(ClassObject& obj);
  void NoteObjectReclaimed(ClassObject& obj);
  void NoteForce(int reason, const Variable* var, const Stmt* stmt,
                 std::string prefix);
  void NoteDisabled(const Stmt* disable, std::string prefix);

  int DispatchReset();

  int DispatchRestart();

  int Get(int property, VpiHandle obj);

  PLI_INT64 Get64(int property, VpiHandle obj);

  int SmallestModuleTimePrecision() const;

  PLI_BYTE8* GetStr(int property, VpiHandle obj);
  const char* GetStrRaw(int property, VpiHandle obj);
  int FreeObject(VpiHandle obj);
  int Control(int operation, int arg0 = 0, VpiHandle scope = nullptr);

  int ControlCoverage(int operation, int coverage_type, VpiHandle scope_handle,
                      const std::string& name);

  CoverageControlState& GetCoverageControlState();

  bool ChkError(s_vpi_error_info* info);

  void SetInvocationArguments(const std::string& tool_name,
                              const std::vector<std::string>& options);

  bool GetVlogInfo(s_vpi_vlog_info* info);

  int Flush();

  void WriteOutputChannel(std::string_view text);
  void WriteLogFile(std::string_view text);

  void ConnectOutputChannel(std::ostream* out);
  const std::string& OutputChannelBuffer() const {
    return channels_.output_channel_buffer;
  }
  const std::string& LogFileBuffer() const { return channels_.log_file_buffer; }
  const std::string& OutputChannelFlushed() const {
    return channels_.output_channel_flushed;
  }
  const std::string& LogFileFlushed() const {
    return channels_.log_file_flushed;
  }
  void SetFlushShouldFail(bool fail) { channels_.flush_should_fail = fail; }

  PLI_UINT32 McdOpen(const std::string& filename);

  PLI_UINT32 McdClose(PLI_UINT32 mcd);

  void RegisterFopenMcdFile(const std::string& filename, PLI_UINT32 mcd) {
    channels_.mcd_open_files[filename] = mcd;
    channels_.mcd_allocated_channels |= mcd;
  }
  PLI_UINT32 McdForFile(const std::string& filename) const {
    auto it = channels_.mcd_open_files.find(filename);
    return it == channels_.mcd_open_files.end() ? 0u : it->second;
  }
  bool IsMcdFileOpen(const std::string& filename) const {
    return channels_.mcd_open_files.find(filename) !=
           channels_.mcd_open_files.end();
  }
  void SetMcdOpenShouldFail(bool fail) {
    channels_.mcd_open_should_fail = fail;
  }

  PLI_INT32 McdFlush(PLI_UINT32 mcd);

  PLI_BYTE8* McdName(PLI_UINT32 cd);

  PLI_INT32 McdPrintf(PLI_UINT32 mcd, std::string_view text);

  PLI_INT32 Printf(std::string_view text);

  void WriteMcdChannel(PLI_UINT32 channel, std::string_view text);
  const std::string& McdChannelBuffer(PLI_UINT32 channel) const;
  const std::string& McdChannelFlushed(PLI_UINT32 channel) const;
  void SetMcdFlushShouldFail(bool fail) {
    channels_.mcd_flush_should_fail = fail;
  }

  VpiHandle HandleMulti(int type, VpiHandle ref1, VpiHandle ref2);

  int CompareObjects(VpiHandle obj1, VpiHandle obj2);

  VpiHandle CreateHandleFor(VpiHandle object);

  VpiHandle CreateAssertionCallbackObject(std::uint64_t placed_handle);

  void ReleaseHandle(VpiHandle handle);

  PLI_INT32 ReleaseHandleStatus(VpiHandle handle);

  bool HandleReleased(VpiHandle handle) const;

  bool HandleValid(VpiHandle handle) const;

  bool HandleSurvivesRestart(VpiHandle handle) const;

  void ReleaseHandlesForRestart();

  void ReleaseFrameOrThreadObject(VpiHandle root);

  void ReleaseClassObject(VpiHandle class_object);

  bool SetDefaultCompatibilityMode(int mode);

  int DefaultCompatibilityMode() const { return default_compat_mode_; }

  int EffectiveCompatibilityMode(bool uses_mechanism1,
                                 int mechanism1_mode) const;

  VpiHandle CreateModule(std::string_view name, std::string full_name);

  VpiHandle CreatePort(std::string_view name, int direction, VpiHandle parent);

  VpiHandle CreateParameter(std::string_view name, int int_value);

  VpiHandle CreateAssertion(std::string_view name, int type);

  VpiHandle CreateNetObj(std::string_view name, Net* net_ptr, int width);

  VpiHandle CreateRegArray(std::string_view name, int array_type,
                           const std::vector<std::vector<int>>& dim_indices,
                           const std::vector<Variable*>& elements);

  void PutValueArray(VpiHandle obj, s_vpi_arrayvalue* arrayvalue_p,
                     int* index_p, unsigned int num);

  void GetValueArray(VpiHandle obj, s_vpi_arrayvalue* arrayvalue_p,
                     int* index_p, unsigned int num);

  const std::vector<s_vpi_systf_data>& RegisteredSystfs() const {
    return systfs_;
  }

  int SystfResultSizeBits(const s_vpi_systf_data& data);

  const std::vector<s_cb_data>& RegisteredCallbacks() const;

  void MarkElaborationStarted() { elaboration_started_ = true; }
  bool ElaborationStarted() const { return elaboration_started_; }

  void SetToolPhase(VpiToolPhase phase) { tool_phase_ = phase; }
  VpiToolPhase ToolPhase() const { return tool_phase_; }

  bool RoutineIsUnavailableNow(VpiRoutine routine);

  void SetSimulationProgressedIntoTimeSlice(bool progressed);
  bool SimulationProgressedIntoTimeSlice() const;
  void SetAtReadOnlySynchTime(bool at_read_only) {
    at_read_only_synch_time_ = at_read_only;
  }
  bool AtReadOnlySynchTime() const { return at_read_only_synch_time_; }

  bool StopRequested() const { return control_.stop_requested; }
  bool FinishRequested() const { return control_.finish_requested; }
  int StopDiagLevel() const { return control_.stop_diag_level; }
  int FinishDiagLevel() const { return control_.finish_diag_level; }
  VpiHandle InteractiveScope() const { return control_.interactive_scope; }
  void EnterApplicationRoutine() { ++control_.routines_running; }
  void LeaveApplicationRoutine();
  void NoteInteractiveScope(VpiHandle scope);

  void SetActiveFrame(VpiHandle frame);
  VpiHandle ActiveFrame() const;

  void SetCurrentSystfCall(VpiHandle call) { current_systf_call_ = call; }
  VpiHandle CurrentSystfCall() const { return current_systf_call_; }

  void NoteTimeFormatCall(const Expr* call_site, SimContext& ctx);
  VpiHandle ActiveTimeFormatCall() const { return active_time_format_call_; }

  void SetSaveRestartLocation(std::string path) {
    save_restart_location_ = std::move(path);
  }
  const std::string& SaveRestartLocation() const {
    return save_restart_location_;
  }

  const s_vpi_error_info& LastError() const { return last_error_; }

  void ResetErrorStatus() { last_error_ = {}; }

  VpiHandle ThreadObjectFor(Process* proc);
  void RefreshThreadObjects();
  void RefreshRunObjects();
  VpiHandle ClassObjectOf(VpiObject& class_var);

  VpiHandle ActivateFrame(const void*& thread, const Expr* call);
  void RestoreActiveFrame(VpiHandle previous, const void* thread);

  void NoteErrorRecorded();

 private:
  VpiHandle AllocObject();

  VpiHandle MakeSystfCallObject(const s_vpi_systf_data& data,
                                const Expr* call_site, SimContext& ctx,
                                Arena& arena, bool evaluate_args);

  VpiHandle DesignScopeChild(VpiHandle parent, std::string_view part,
                             std::string_view full_path);
  VpiHandle DesignObjectForFlatName(std::string_view flat_name);

  void AttachModulePathDelays(SimContext& sim_ctx);
  void AttachTimingChecks(SimContext& sim_ctx);
  void AttachModuleDefNames(SimContext& sim_ctx);
  void AttachUdpDefns(const RtlirDesign* design);
  void AttachInstanceObjects(const RtlirDesign* design);
  void AttachPackages(const RtlirDesign* design);
  void AttachInstanceContents(const RtlirDesign* design);
  void AttachInstanceDefinitions(const RtlirDesign* design);
  void AttachContinuousAssignments(const RtlirDesign* design,
                                   const VpiCallBuild& calls);
  void AttachVariableFacts(const RtlirDesign* design);

  void AttachNettypeDeclarations(const RtlirDesign* design);
  void MakeNettypeDecls(VpiHandle scope, const std::vector<ModuleItem*>& items,
                        const std::vector<RtlirImport>& imports);

  void AttachSourceDelayExpressions(SimContext& sim_ctx,
                                    const RtlirDesign* design);

  void ReleaseHandleWithCallbacks(VpiObject* object);

  void ReleaseHandleSubtree(VpiObject* root);

  std::vector<s_vpi_systf_data> systfs_;
  std::vector<VpiObject*> systf_objects_;
  std::unordered_map<size_t, int> systf_result_bits_;
  std::vector<s_cb_data> callbacks_;
  std::vector<VpiHandle> cb_handles_;
  std::unordered_map<std::string_view, VpiObject*> object_map_;
  std::vector<VpiObject*> all_objects_;
  Scheduler* scheduler_ = nullptr;
  int sim_time_unit_ = 0;
  std::vector<VpiTimeQueueSlot> time_queue_slots_;
  bool elaboration_started_ = false;
  VpiToolPhase tool_phase_ = VpiToolPhase::kFull;
  VpiControlRequests control_;
  std::unordered_map<const void*, VpiHandle> active_frames_;
  VpiHandle current_systf_call_ = nullptr;
  VpiCallSiteObjects call_site_objects_;
  VpiCallSiteObjects invoked_call_objects_;
  std::unordered_map<const VpiObject*, std::size_t> run_entry_index_;
  VpiStmtObjects stmt_objects_;
  bool stmt_callbacks_registered_ = false;
  VpiCallObjects call_objects_;
  VpiCallBuild CallBuild();

  VpiHandle active_time_format_call_ = nullptr;

  int default_compat_mode_ = 0;
  bool default_compat_mode_selected_ = false;

  VpiChannelState channels_;

  s_vpi_error_info last_error_ = {};

  int current_callback_reason_ = -1;
  void Deliver(s_cb_data data);
  VpiHandle MadeClassObject(ClassObject& obj);

  bool sim_progressed_into_time_slice_ = false;
  bool at_read_only_synch_time_ = false;

  std::unordered_map<int, std::vector<char>> save_data_;
  std::unordered_map<int, std::size_t> save_data_cursor_;

  CoverageControlState coverage_control_;

  std::string product_ = "DeltaHDL";
  std::string version_ = "0.1.0";

  std::vector<std::string> invocation_args_;
  std::vector<std::string> invocation_file_args_;
  std::vector<PLI_BYTE8*> invocation_argv_;

  VpiValuePools value_pools_;

  std::deque<std::string> name_pool_;
  std::unordered_set<std::string_view> dotted_escaped_names_;

  bool dispatching_error_callbacks_ = false;

  SimContext* sim_ctx_ = nullptr;
  std::unordered_map<const void*, VpiObject*> run_objects_;

  std::string get_str_buffer_;

  std::string save_restart_location_;

  std::vector<unsigned char> value_array_storage_;
};

}  // namespace delta
