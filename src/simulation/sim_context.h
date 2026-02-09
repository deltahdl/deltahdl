#pragma once

#include <cstdint>
#include <cstdio>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/class_object.h"
#include "simulation/net.h"
#include "simulation/scheduler.h"
#include "simulation/sync_objects.h"
#include "simulation/variable.h"

namespace delta {

class DiagEngine;
class DpiContext;
class VcdWriter;
struct ModuleItem;
struct Process;

// §6.19: Enum member information for built-in enum methods.
struct EnumMemberInfo {
  std::string_view name;
  uint64_t value = 0;
};

// §6.19: Enum type descriptor for method dispatch.
struct EnumTypeInfo {
  std::string_view type_name;
  std::vector<EnumMemberInfo> members;
};

class SimContext {
 public:
  SimContext(Scheduler& sched, Arena& arena, DiagEngine& diag,
             uint32_t seed = 0);

  Variable* FindVariable(std::string_view name);
  Variable* CreateVariable(std::string_view name, uint32_t width);

  Net* FindNet(std::string_view name);
  Net* CreateNet(std::string_view name, NetType type, uint32_t width);

  Scheduler& GetScheduler() { return scheduler_; }
  Arena& GetArena() { return arena_; }
  DiagEngine& GetDiag() { return diag_; }
  SimTime CurrentTime() const { return scheduler_.CurrentTime(); }

  void RequestStop() { stop_requested_ = true; }
  bool StopRequested() const { return stop_requested_; }

  void RegisterFinalProcess(Process* proc);
  void RunFinalBlocks();

  void AddSensitivity(std::string_view signal, Process* proc);
  const std::vector<Process*>& GetSensitiveProcesses(
      std::string_view signal) const;

  void RegisterFunction(std::string_view name, ModuleItem* item);
  ModuleItem* FindFunction(std::string_view name);

  void PushScope();
  void PopScope();
  void PushStaticScope(std::string_view func_name);
  void PopStaticScope(std::string_view func_name);
  Variable* FindLocalVariable(std::string_view name);
  Variable* CreateLocalVariable(std::string_view name, uint32_t width);
  // §13.5.2: Alias an existing variable into the current scope (pass by ref).
  void AliasLocalVariable(std::string_view name, Variable* var);

  void SetVcdWriter(VcdWriter* vcd) { vcd_writer_ = vcd; }
  VcdWriter* GetVcdWriter() { return vcd_writer_; }

  void SetDpiContext(DpiContext* dpi) { dpi_context_ = dpi; }
  DpiContext* GetDpiContext() { return dpi_context_; }

  void SetCurrentProcess(Process* proc) { current_process_ = proc; }
  Process* CurrentProcess() const { return current_process_; }
  bool IsReactiveContext() const;

  const std::unordered_map<std::string_view, Variable*>& GetVariables() const {
    return variables_;
  }

  int32_t Random32();
  uint32_t Urandom32();
  uint32_t UrandomRange(uint32_t min_val, uint32_t max_val);

  // §6.19: Enum type registration and lookup.
  void RegisterEnumType(std::string_view name, const EnumTypeInfo& info);
  const EnumTypeInfo* FindEnumType(std::string_view name) const;
  void SetVariableEnumType(std::string_view var_name,
                           std::string_view type_name);
  const EnumTypeInfo* GetVariableEnumType(std::string_view var_name) const;

  // Plus-args (§20.11)
  void AddPlusArg(std::string arg);
  const std::vector<std::string>& GetPlusArgs() const { return plus_args_; }

  // File descriptor management (§21.3)
  int OpenFile(std::string_view filename, std::string_view mode);
  void CloseFile(int fd);
  FILE* GetFileHandle(int fd);

  // §15.3: Semaphore object management.
  SemaphoreObject* CreateSemaphore(std::string_view name, int32_t keys);
  SemaphoreObject* FindSemaphore(std::string_view name);

  // §15.4: Mailbox object management.
  MailboxObject* CreateMailbox(std::string_view name, int32_t bound);
  MailboxObject* FindMailbox(std::string_view name);

  // §15.5.2: Event triggered state management.
  void SetEventTriggered(std::string_view name);
  bool IsEventTriggered(std::string_view name) const;

  // §8: Class type registry and object management.
  void RegisterClassType(std::string_view name, ClassTypeInfo* info);
  ClassTypeInfo* FindClassType(std::string_view name);

  // Allocate a new class object, returning its handle ID (>0).
  uint64_t AllocateClassObject(ClassObject* obj);
  ClassObject* GetClassObject(uint64_t handle) const;

  // §8.11: `this` pointer management for method calls.
  void PushThis(ClassObject* obj);
  void PopThis();
  ClassObject* CurrentThis() const;

  // §14: Clocking manager access.
  void SetClockingManager(class ClockingManager* mgr) { clocking_mgr_ = mgr; }
  class ClockingManager* GetClockingManager() { return clocking_mgr_; }

  // §19: Coverage database access.
  void SetCoverageDB(class CoverageDB* db) { coverage_db_ = db; }
  class CoverageDB* GetCoverageDB() { return coverage_db_; }

 private:
  Scheduler& scheduler_;
  Arena& arena_;
  DiagEngine& diag_;
  std::mt19937 rng_;
  std::unordered_map<std::string_view, Variable*> variables_;
  std::unordered_map<std::string_view, Net*> nets_;
  std::unordered_map<std::string_view, ModuleItem*> functions_;
  std::vector<std::unordered_map<std::string_view, Variable*>> scope_stack_;
  // §13.3.1: Static function frames persist between calls.
  std::unordered_map<std::string_view,
                     std::unordered_map<std::string_view, Variable*>>
      static_frames_;
  std::vector<Process*> final_processes_;
  std::unordered_map<std::string_view, std::vector<Process*>> sensitivity_map_;
  static const std::vector<Process*> kEmptyProcessList;
  VcdWriter* vcd_writer_ = nullptr;
  DpiContext* dpi_context_ = nullptr;
  Process* current_process_ = nullptr;
  bool stop_requested_ = false;
  std::vector<std::string> plus_args_;
  std::unordered_map<int, FILE*> file_descriptors_;
  int next_fd_ = 3;  // Start after stdin/stdout/stderr.
  // §6.19: Enum type info and variable-to-enum-type mapping.
  std::unordered_map<std::string_view, EnumTypeInfo> enum_types_;
  std::unordered_map<std::string_view, std::string_view> var_enum_types_;
  // §15.3: Semaphore objects.
  std::unordered_map<std::string_view, SemaphoreObject*> semaphores_;
  // §15.4: Mailbox objects.
  std::unordered_map<std::string_view, MailboxObject*> mailboxes_;
  // §15.5.2: Event triggered timestamps (ticks when last triggered).
  std::unordered_map<std::string_view, uint64_t> event_triggered_;
  // §8: Class type registry.
  std::unordered_map<std::string_view, ClassTypeInfo*> class_types_;
  // §8: Object heap — maps handle ID to ClassObject.
  std::unordered_map<uint64_t, ClassObject*> class_objects_;
  uint64_t next_handle_id_ = 1;
  // §8.11: Stack of `this` pointers for nested method calls.
  std::vector<ClassObject*> this_stack_;
  // §14: Clocking manager.
  class ClockingManager* clocking_mgr_ = nullptr;
  // §19: Coverage database.
  class CoverageDB* coverage_db_ = nullptr;
};

}  // namespace delta
