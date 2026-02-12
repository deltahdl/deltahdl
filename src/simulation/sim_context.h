#pragma once

#include <cstdint>
#include <cstdio>
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

// §7.2: Struct field descriptor for packed struct layout.
struct StructFieldInfo {
  std::string_view name;
  uint32_t bit_offset = 0;
  uint32_t width = 0;
  DataTypeKind type_kind = DataTypeKind::kLogic;
};

// §7.2: Struct type descriptor for field-level access.
struct StructTypeInfo {
  std::string_view type_name;
  std::vector<StructFieldInfo> fields;
  uint32_t total_width = 0;
  bool is_packed = false;
};

// §7.10: Queue runtime storage.
struct QueueObject {
  std::vector<Logic4Vec> elements;
  uint32_t elem_width = 32;
  int32_t max_size = -1;  // -1 = unbounded.
};

// §7.8: Associative array runtime storage.
struct AssocArrayObject {
  std::map<int64_t, Logic4Vec> int_data;
  std::map<std::string, Logic4Vec> str_data;
  uint32_t elem_width = 32;
  bool is_string_key = false;
  bool has_default = false;
  Logic4Vec default_value;
  uint32_t Size() const;
};

// §7.4/§7.5/§7.10: Array metadata for method dispatch.
struct ArrayInfo {
  uint32_t lo = 0;             // Low index of unpacked dimension.
  uint32_t size = 0;           // Number of elements.
  uint32_t elem_width = 32;    // Width of each element in bits.
  bool is_descending = false;  // §7.4: true for [hi:lo] range.
  bool is_dynamic = false;     // §7.5: dynamic array (new/delete).
  bool is_queue = false;       // §7.10: queue ($).
};

class SimContext {
 public:
  SimContext(Scheduler& sched, Arena& arena, DiagEngine& diag,
             uint32_t seed = 0);

  Variable* FindVariable(std::string_view name);
  Variable* CreateVariable(std::string_view name, uint32_t width);

  Net* FindNet(std::string_view name);
  Net* CreateNet(std::string_view name, NetType type, uint32_t width,
                 Strength charge_strength = Strength::kMedium,
                 uint64_t decay_ticks = 0);

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

  // §6.12: Real variable registration and lookup.
  void RegisterRealVariable(std::string_view name);
  bool IsRealVariable(std::string_view name) const;

  // §6.16: String variable registration and lookup.
  void RegisterStringVariable(std::string_view name);
  bool IsStringVariable(std::string_view name) const;

  // §6.20.7: Unbounded parameter ($) tracking.
  void RegisterUnboundedParam(std::string_view name);
  bool IsUnboundedParam(std::string_view name) const;

  // §6.19: Enum type registration and lookup.
  void RegisterEnumType(std::string_view name, const EnumTypeInfo& info);
  const EnumTypeInfo* FindEnumType(std::string_view name) const;
  void SetVariableEnumType(std::string_view var_name,
                           std::string_view type_name);
  const EnumTypeInfo* GetVariableEnumType(std::string_view var_name) const;

  // §7.2: Struct type registration and lookup.
  void RegisterStructType(std::string_view name, const StructTypeInfo& info);
  const StructTypeInfo* FindStructType(std::string_view name) const;
  void SetVariableStructType(std::string_view var_name,
                             std::string_view type_name);
  const StructTypeInfo* GetVariableStructType(std::string_view var_name) const;

  // §7.4/§7.5/§7.10: Array metadata registration and lookup.
  void RegisterArray(std::string_view name, const ArrayInfo& info);
  ArrayInfo* FindArrayInfo(std::string_view name);
  const ArrayInfo* FindArrayInfo(std::string_view name) const;

  // §7.10: Queue management.
  QueueObject* CreateQueue(std::string_view name, uint32_t elem_width,
                           int32_t max_size = -1);
  QueueObject* FindQueue(std::string_view name);

  // §7.8: Associative array management.
  AssocArrayObject* CreateAssocArray(std::string_view name, uint32_t elem_width,
                                     bool is_string_key);
  AssocArrayObject* FindAssocArray(std::string_view name);

  // §7.3.2: Tagged union tag management.
  void SetVariableTag(std::string_view var_name, std::string_view tag);
  std::string_view GetVariableTag(std::string_view var_name) const;

  // §20.6.2: Type name to bit width, for $bits(type).
  void RegisterTypeWidth(std::string_view name, uint32_t width);
  uint32_t FindTypeWidth(std::string_view name) const;

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
  void SetVariableClassType(std::string_view var, std::string_view type);
  std::string_view GetVariableClassType(std::string_view var) const;

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
  // §6.12: Real variable tracking.
  std::unordered_set<std::string_view> real_vars_;
  // §6.16: String variable tracking.
  std::unordered_set<std::string_view> string_vars_;
  // §6.20.7: Unbounded parameter tracking.
  std::unordered_set<std::string_view> unbounded_params_;
  // §6.19: Enum type info and variable-to-enum-type mapping.
  std::unordered_map<std::string_view, EnumTypeInfo> enum_types_;
  std::unordered_map<std::string_view, std::string_view> var_enum_types_;
  // §7.2: Struct type info and variable-to-struct-type mapping.
  std::unordered_map<std::string_view, StructTypeInfo> struct_types_;
  std::unordered_map<std::string_view, std::string_view> var_struct_types_;
  // §7.4/§7.5/§7.10: Array metadata.
  std::unordered_map<std::string_view, ArrayInfo> array_infos_;
  // §7.10: Queue runtime objects.
  std::unordered_map<std::string_view, QueueObject*> queues_;
  // §7.8: Associative array runtime objects.
  std::unordered_map<std::string_view, AssocArrayObject*> assoc_arrays_;
  // §7.3.2: Tagged union tag tracking (variable name → active tag).
  std::unordered_map<std::string_view, std::string> var_tags_;
  // §15.3: Semaphore objects.
  std::unordered_map<std::string_view, SemaphoreObject*> semaphores_;
  // §15.4: Mailbox objects.
  std::unordered_map<std::string_view, MailboxObject*> mailboxes_;
  // §15.5.2: Event triggered timestamps (ticks when last triggered).
  std::unordered_map<std::string_view, uint64_t> event_triggered_;
  // §8: Class type registry and variable→class type mapping.
  std::unordered_map<std::string_view, ClassTypeInfo*> class_types_;
  std::unordered_map<std::string_view, std::string_view> var_class_types_;
  // §8: Object heap — maps handle ID to ClassObject.
  std::unordered_map<uint64_t, ClassObject*> class_objects_;
  uint64_t next_handle_id_ = 1;
  // §8.11: Stack of `this` pointers for nested method calls.
  std::vector<ClassObject*> this_stack_;
  // §20.6.2: Type name → bit width for $bits(type).
  std::unordered_map<std::string_view, uint32_t> type_widths_;
  // §14: Clocking manager.
  class ClockingManager* clocking_mgr_ = nullptr;
  // §19: Coverage database.
  class CoverageDB* coverage_db_ = nullptr;
};

}  // namespace delta
