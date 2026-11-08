#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <map>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "common/types.h"
#include "parser/ast_type.h"
#include "parser/expr_substitute.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

struct Expr;
struct MailboxObject;
struct ModuleItem;
struct SemaphoreObject;
struct Stmt;

class DeclaredNameTables {
 public:
  void RegisterFunction(std::string_view name, ModuleItem* item);
  ModuleItem* FindFunction(std::string_view name);

  void PushFunctionScope(std::vector<ModuleItem*> functions);
  void PopFunctionScope();
  ModuleItem* FindScopedFunction(std::string_view name) const;

  void RegisterGenBlockSubroutineScope(std::string_view key,
                                       GenBlockSubroutineScope scope);
  const GenBlockSubroutineScope* FindGenBlockSubroutineScope(
      std::string_view key) const;

  void DeclareForkjoinTask(std::string_view key);
  void AddForkjoinDefinition(std::string_view key, std::string_view definition);
  const std::vector<std::string_view>* FindForkjoinTask(
      std::string_view key) const;
  bool HasForkjoinTasks() const { return !forkjoin_tasks_.empty(); }
  const Stmt* FindForkjoinCall(const Expr* call) const;
  void RecordForkjoinCall(const Expr* call, const Stmt* fork);

  void DeclareNamedScope(std::string key) {
    declared_named_scopes_.insert(std::move(key));
  }
  bool DeclaresNamedScope(const std::string& key) const {
    return declared_named_scopes_.contains(key);
  }

  void RegisterModportExpression(std::string key, ModportExpressionPort port);
  const ModportExpressionPort* FindModportExpression(
      std::string_view key) const;
  bool HasModportExpressions() const { return !modport_expressions_.empty(); }
  const Stmt* FindModportExpressionNba(const Stmt* stmt,
                                       const ModportExpressionPort* port) const;
  void RecordModportExpressionNba(const Stmt* stmt,
                                  const ModportExpressionPort* port,
                                  const Stmt* nba);

  void RegisterLetDecl(std::string_view name, ModuleItem* item);
  ModuleItem* FindLetDecl(std::string_view name);

  void RegisterSequenceDecl(std::string_view name, ModuleItem* item);
  ModuleItem* FindSequenceDecl(std::string_view name);
  void RegisterPropertyDecl(std::string_view name, ModuleItem* item);
  ModuleItem* FindPropertyDecl(std::string_view name);

  void RegisterSequenceInstanceEndpoint(const Expr* instance,
                                        std::string_view ep_name);
  std::string_view FindSequenceInstanceEndpoint(const Expr* instance) const;

  bool ConsumeSequenceMatch(std::string_view ep_name, uint64_t matched_ticks,
                            uint64_t now);

  using MatchLocals = std::vector<std::pair<std::string_view, Logic4Vec>>;
  void RecordEndpointLocals(std::string_view ep_name, uint64_t at,
                            std::vector<MatchLocals> matches);
  const std::vector<MatchLocals>* EndpointLocals(std::string_view ep_name,
                                                 uint64_t at) const;

  void RegisterCheckerActuals(std::string inst_prefix, ActualsByFormal actuals);
  const ActualsByFormal* CheckerActuals(const std::string& inst_prefix) const;

  void RegisterRealVariable(std::string_view name);
  bool IsRealVariable(std::string_view name) const;

  void RegisterImportedName(std::string_view name);
  bool IsImportedName(std::string_view name) const;
  void RegisterBlockVariable(std::string_view name);
  bool IsBlockVariable(std::string_view name) const;
  void RegisterBlockParamOverride(std::string_view prefix, const Stmt* decl,
                                  Expr* init);
  Expr* BlockParamOverride(std::string_view prefix, const Stmt* decl) const;

  void RegisterSubroutinePackage(const ModuleItem* subroutine,
                                 std::string_view pkg);
  std::string_view SubroutinePackage(const ModuleItem* subroutine) const;
  void RegisterStaticFrameOwner(const ModuleItem* subroutine,
                                std::string_view owner);
  std::string_view StaticFrameOwner(const ModuleItem* subroutine) const;
  void RegisterGenBlockSubroutineDepth(const ModuleItem* subroutine,
                                       size_t depth);
  size_t GenBlockSubroutineDepth(const ModuleItem* subroutine) const;
  const std::vector<const ModuleItem*>& OwnedSubroutines() const {
    return owned_subroutines_;
  }
  void RegisterPackageImport(std::string_view pkg, std::string_view imported,
                             std::string_view item);
  std::vector<std::string> PackageScopedKeys(std::string_view pkg,
                                             std::string_view name) const;

  void RegisterNestedDeclScope(std::string_view prefix);

  void RegisterChandleVariable(std::string_view name);
  bool IsChandleVariable(std::string_view name) const;

  void RegisterUnboundedParam(std::string_view name);
  bool IsUnboundedParam(std::string_view name) const;

  void RegisterEnumType(std::string_view name, const EnumTypeInfo& info);
  const EnumTypeInfo* FindEnumType(std::string_view name) const;
  void SetVariableEnumType(std::string_view var_name,
                           std::string_view type_name);
  const EnumTypeInfo* GetVariableEnumType(std::string_view var_name) const;
  void SetStorageEnumType(const Variable* var, std::string_view type_name);
  const EnumTypeInfo* GetStorageEnumType(const Variable* var) const;
  const EnumTypeInfo* FindEnumTypeDeclaringMember(std::string_view member,
                                                  std::string_view scope) const;

  void RegisterStructType(std::string_view name, const StructTypeInfo& info);
  const StructTypeInfo* FindStructType(std::string_view name) const;
  void SetVariableStructType(std::string_view var_name,
                             std::string_view type_name);
  const StructTypeInfo* GetVariableStructType(std::string_view var_name) const;
  std::string_view VariableStructTypeName(std::string_view var_name) const;

  void RegisterTypeWidth(std::string_view name, uint32_t width);
  uint32_t FindTypeWidth(std::string_view name) const;

  void RegisterTypeKind(std::string_view name, DataTypeKind kind);
  DataTypeKind FindTypeKind(std::string_view name) const;

  void RegisterTypeSigned(std::string_view name, bool is_signed);
  bool FindTypeSigned(std::string_view name) const;

  void RegisterTypeRange(std::string_view name, PackedRange range);
  std::optional<PackedRange> FindTypeRange(std::string_view name) const;

  void RegisterTypeTarget(std::string_view name, std::string_view target);
  std::string_view FindTypeTarget(std::string_view name) const;
  size_t TypeTargetCount() const;

  void RegisterTypeDeclaration(std::string_view name, const ModuleItem* item);
  const DataType* FindTypeDeclaration(std::string_view name) const;
  std::string_view FindPackageTypedefKey(std::string_view name) const;
  const DataType* PackedTypeBehind(const DataType& type) const;
  const ModuleItem* FindTypedefItem(std::string_view name) const;
  size_t TypeDeclarationCount() const;

  void BindSemaphoreHandle(const Variable* var, SemaphoreObject* sem);
  SemaphoreObject* SemaphoreOfHandle(const Variable* var) const;
  void BindMailboxHandle(const Variable* var, MailboxObject* mbx);
  MailboxObject* MailboxOfHandle(const Variable* var) const;
  uint64_t RegisterEventIdentity(Variable* event);
  Variable* EventOfIdentity(uint64_t identity) const;
  void RecordContainedSemaphore(SemaphoreObject* sem);
  SemaphoreObject* ContainedSemaphore(uint64_t identity) const;
  void RecordContainedMailbox(MailboxObject* mbx);
  MailboxObject* ContainedMailbox(uint64_t identity) const;
  std::vector<const MailboxObject*> HeldMailboxes() const;

  void RegisterInstanceType(std::string_view prefix, std::string_view type);
  std::string_view FindInstanceType(std::string_view prefix) const;
  void RegisterInstanceConfig(std::string_view prefix, std::string_view config);
  std::string_view FindInstanceConfig(std::string_view prefix) const;
  std::string InstantiatingPrefix(std::string_view prefix) const;
  std::vector<std::string> NestedDeclOuterScopes(std::string_view prefix) const;
  template <typename T>
  T* FindInNestedDeclOuterScopes(
      const std::unordered_map<std::string_view, T*>& table,
      std::string_view prefix, std::string_view name) const {
    for (const std::string& scope : NestedDeclOuterScopes(prefix)) {
      auto it = table.find(scope + std::string(name));
      if (it != table.end()) return it->second;
    }
    return nullptr;
  }

  void RegisterInstancePath(std::string_view prefix, std::string path);
  std::string_view FindInstancePath(std::string_view prefix) const;
  std::string_view FindInstanceKeyOfPath(std::string_view path) const;

  void RegisterInterfacePortInstance(std::string_view port_key,
                                     std::string instance_key);
  std::string_view FindInterfacePortInstance(std::string_view port_key) const;

  void RegisterTopModule(std::string_view name);
  bool IsTopModule(std::string_view name) const;
  std::string_view FirstTopModule() const { return first_top_module_; }
  void RegisterParallelTop(std::string_view name);
  bool IsParallelTop(std::string_view name) const;
  std::string RootedStorageKey(std::string_view rest) const;

  void RegisterVariableClassTypeParams(std::string_view var,
                                       const std::vector<DataType>* params);
  const std::vector<DataType>* FindVariableClassTypeParams(
      std::string_view var) const;

  uint64_t VirtualInterfaceHandle(std::string_view scope);
  std::string_view VirtualInterfaceScope(uint64_t handle) const;

  void RegisterVirtualInterfaceVar(Variable* v);
  bool IsVirtualInterfaceVar(const Variable* v) const;
  bool VirtualInterfaceIsBound(const Variable* v) const;
  std::string_view VirtualInterfaceBinding(const Variable* v) const;

 protected:
  std::function<std::string()> running_unit_scope_;
  template <typename Table>
  std::string_view UnitKeyIn(const Table& table, std::string_view name,
                             std::string& scoped) const {
    scoped = running_unit_scope_();
    if (scoped.empty()) return name;
    scoped += "::";
    scoped += name;
    return table.contains(scoped) ? std::string_view(scoped) : name;
  }

  std::unordered_map<std::string_view, ModuleItem*> functions_;
  std::vector<std::vector<ModuleItem*>> function_scopes_;
  std::unordered_map<std::string_view, GenBlockSubroutineScope>
      gen_block_subroutine_scopes_;
  std::unordered_map<std::string, std::vector<std::string_view>>
      forkjoin_tasks_;
  std::unordered_map<const Expr*, const Stmt*> forkjoin_calls_;
  std::unordered_set<std::string> declared_named_scopes_;
  std::unordered_map<std::string, ModportExpressionPort> modport_expressions_;
  std::map<std::pair<const Stmt*, const ModportExpressionPort*>, const Stmt*>
      modport_expression_nbas_;
  std::unordered_map<std::string_view, ModuleItem*> let_decls_;
  std::unordered_map<std::string_view, ModuleItem*> sequence_decls_;
  std::unordered_map<std::string_view, ModuleItem*> property_decls_;
  std::unordered_map<const Expr*, std::string_view> sequence_instance_eps_;
  std::map<std::string, uint64_t, std::less<>> sequence_match_reads_;
  struct EndpointMatches {
    uint64_t at = 0;
    std::vector<MatchLocals> matches;
  };
  std::unordered_map<std::string, EndpointMatches> endpoint_locals_;
  std::unordered_map<std::string, ActualsByFormal> checker_actuals_;

  std::unordered_set<std::string_view> real_vars_;

  std::unordered_set<std::string_view> imported_names_;
  std::unordered_set<std::string_view> block_variables_;
  std::map<std::pair<std::string, const Stmt*>, Expr*> block_param_overrides_;
  std::unordered_map<const ModuleItem*, std::string_view> subroutine_packages_;
  std::unordered_map<const ModuleItem*, std::string_view> static_frame_owners_;
  std::unordered_map<const ModuleItem*, size_t> gen_block_subroutine_depths_;
  std::vector<const ModuleItem*> owned_subroutines_;
  struct PackageImport {
    std::string_view imported;
    std::string_view item;
  };
  std::unordered_map<std::string_view, std::vector<PackageImport>>
      package_imports_;
  std::unordered_set<std::string> nested_decl_scopes_;

  std::unordered_set<std::string_view> chandle_vars_;

  std::unordered_set<std::string_view> unbounded_params_;

  std::unordered_map<std::string_view, EnumTypeInfo> enum_types_;
  std::unordered_map<std::string_view, std::string_view> var_enum_types_;
  std::unordered_map<const Variable*, std::string_view> storage_enum_types_;

  std::unordered_map<std::string_view, StructTypeInfo> struct_types_;
  std::unordered_map<std::string_view, std::string_view> var_struct_types_;

  std::unordered_map<std::string_view, uint32_t> type_widths_;
  std::unordered_map<std::string_view, DataTypeKind> type_kinds_;
  std::unordered_map<std::string_view, bool> type_signed_;
  std::unordered_map<std::string_view, PackedRange> type_ranges_;

  std::unordered_map<std::string_view, std::string_view> type_targets_;
  std::unordered_map<std::string_view, const ModuleItem*> type_declarations_;
  std::unordered_map<const Variable*, SemaphoreObject*> semaphore_handles_;
  std::unordered_map<const Variable*, MailboxObject*> mailbox_handles_;
  std::unordered_map<uint64_t, Variable*> event_identities_;
  std::unordered_map<uint64_t, SemaphoreObject*> contained_semaphores_;
  std::unordered_map<uint64_t, MailboxObject*> contained_mailboxes_;

  std::unordered_map<std::string, std::string> instance_types_;
  std::unordered_map<std::string, std::string> instance_configs_;
  std::unordered_map<std::string, std::string> instance_paths_;
  std::unordered_map<std::string, std::string> instance_keys_by_path_;
  std::unordered_map<std::string, std::string> interface_port_instances_;
  std::unordered_set<std::string> top_module_names_;
  std::string first_top_module_;
  std::unordered_set<std::string> parallel_top_names_;
  std::unordered_map<std::string_view, const std::vector<DataType>*>
      var_class_type_params_;

  std::vector<std::string> vi_instance_scopes_;
  std::unordered_map<std::string, uint64_t> vi_instance_handles_;
};

std::vector<std::string> GenerateBlockKeys(
    std::string_view inst_prefix, const std::vector<std::string>& gen_prefixes,
    std::string_view name);

}  // namespace delta
