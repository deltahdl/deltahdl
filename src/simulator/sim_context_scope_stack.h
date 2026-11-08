#pragma once

#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "simulator/scope.h"

namespace delta {

struct DataType;
struct ModuleItem;
struct Stmt;
struct Variable;

class ScopeStack {
 public:
  void PushScope(std::string_view package = {});
  void EnterSubroutineScope(std::string_view package);
  void PopScope();
  Scope DetachScope();
  void RestoreScope(Scope frame);
  std::vector<Scope> SwapScopeStack(std::vector<Scope> new_stack);
  bool HasLocalScope() const { return !scope_stack_.empty(); }
  std::vector<Scope>::const_reverse_iterator VisibleFramesEnd() const;
  Variable* FindLocalVariable(std::string_view name);
  void DeclareLocalLet(std::string_view name, ModuleItem* let);
  ModuleItem* FindLocalLet(std::string_view name) const;
  bool InnermostScopeDeclares(std::string_view name) const;
  const Scope* PackageFrame() const;
  void BindLocalVariable(std::string_view name, Variable* var);
  void AliasLocalVariable(std::string_view name, Variable* var);
  void BindScopeTypeActual(std::string_view name, const DataType* actual);
  bool RecordLocalClassType(std::string_view name, std::string_view type);
  const std::string_view* FindLocalClassType(std::string_view name) const;
  const DataType* FindScopeTypeActual(std::string_view name) const;

  void PushFuncName(std::string_view name);
  void PopFuncName();
  std::string_view CurrentFuncName() const;
  std::string_view StmtFrameName(const Stmt* stmt);
  std::string_view InnermostStmtFrame() const;
  const std::vector<std::string_view>& FuncNameStack() const {
    return func_name_stack_;
  }
  std::vector<FrameOwnerEntry>& ProcesslessFrameOwners() {
    return processless_frame_owners_;
  }

 protected:
  std::vector<Scope> scope_stack_;
  std::unordered_map<std::string_view,
                     std::unordered_map<std::string_view, Variable*>>
      static_frames_;
  std::vector<std::string_view> func_name_stack_;
  std::vector<FrameOwnerEntry> processless_frame_owners_;
  std::unordered_map<const Stmt*, std::string> stmt_frames_;
  std::unordered_set<const char*> stmt_frame_names_;
};

}  // namespace delta
