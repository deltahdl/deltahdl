#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <iterator>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_stmt.h"
#include "simulator/process.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_scope_stack.h"
#include "simulator/sim_context_type_ref_compares.h"
#include "simulator/variable.h"

namespace delta {

void ScopeStack::PushScope(std::string_view package) {
  scope_stack_.push_back(Scope{{}, {}, {}, {}, package, {}, false, {}, {}, {}});
}

void ScopeStack::EnterSubroutineScope(std::string_view package) {
  if (scope_stack_.empty()) return;
  scope_stack_.back().is_subroutine = true;
  if (!package.empty()) scope_stack_.back().package = package;
}

const ModuleItem* SimContext::EnterSubroutinePackage(const ModuleItem* func) {
  if (func != nullptr) EnterSubroutineScope(SubroutinePackage(func));
  return func;
}

void ScopeStack::BindLocalVariable(std::string_view name, Variable* var) {
  if (!scope_stack_.empty()) scope_stack_.back().vars[name] = var;
}

void ScopeStack::BindScopeTypeActual(std::string_view name,
                                     const DataType* actual) {
  if (!scope_stack_.empty()) scope_stack_.back().type_actuals[name] = actual;
}

const DataType* ScopeStack::FindScopeTypeActual(std::string_view name) const {
  for (auto it = scope_stack_.crbegin(); it != VisibleFramesEnd(); ++it) {
    auto found = it->type_actuals.find(name);
    if (found != it->type_actuals.end()) return found->second;
  }
  return nullptr;
}

bool ScopeStack::RecordLocalClassType(std::string_view name,
                                      std::string_view type) {
  for (auto it = scope_stack_.rbegin(); it != scope_stack_.rend(); ++it) {
    if (it->vars.count(name) != 0) {
      it->class_types[name] = type;
      return true;
    }
    if (it->is_subroutine) break;
  }
  return false;
}

const std::string_view* ScopeStack::FindLocalClassType(
    std::string_view name) const {
  for (auto it = scope_stack_.crbegin(); it != VisibleFramesEnd(); ++it) {
    if (it->vars.count(name) == 0) continue;
    auto found = it->class_types.find(name);
    return found != it->class_types.end() ? &found->second : nullptr;
  }
  return nullptr;
}

const Scope* ScopeStack::PackageFrame() const {
  for (auto it = scope_stack_.rbegin(); it != scope_stack_.rend(); ++it) {
    if (!it->package.empty()) return &*it;
    if (it->is_subroutine) return nullptr;
  }
  return nullptr;
}

void ScopeStack::PopScope() {
  if (!scope_stack_.empty()) scope_stack_.pop_back();
}

Scope ScopeStack::DetachScope() {
  Scope frame = std::move(scope_stack_.back());
  scope_stack_.pop_back();
  return frame;
}

void ScopeStack::RestoreScope(Scope frame) {
  scope_stack_.push_back(std::move(frame));
}

std::vector<Scope> ScopeStack::SwapScopeStack(std::vector<Scope> new_stack) {
  auto old = std::move(scope_stack_);
  scope_stack_ = std::move(new_stack);
  return old;
}

std::string_view SimContext::StaticFrameKey(std::string_view name) {
  const std::vector<FrameOwnerEntry>& owners =
      current_process_ != nullptr ? current_process_->frame_owners
                                  : processless_frame_owners_;
  if (!owners.empty() && !owners.back().owner.empty()) {
    return *arena_.Create<std::string>(std::string(owners.back().owner) +
                                       "::" + std::string(name));
  }
  std::string key(ActiveGenBlockPrefix());
  if (current_process_ != nullptr) key.insert(0, current_process_->inst_prefix);
  if (key.empty()) return name;
  return *arena_.Create<std::string>(key + std::string(name));
}

std::string_view SimContext::ActiveGenBlockPrefix() const {
  if (current_process_ == nullptr) return {};
  return GenBlockPrefixOf(*current_process_);
}

void TypeRefCompares::SetLoweringGenBlockPrefix(std::string_view prefix) {
  lowering_gen_prefix_ = std::string(prefix);
}

void TypeRefCompares::RecordTypeRefCompare(std::string scope, const Expr* expr,
                                           bool holds) {
  type_ref_compares_[expr][std::move(scope)] = holds;
}

void TypeRefCompares::RecordUnitTypeRefCompare(const Expr* expr, bool holds) {
  unit_type_ref_compares_[expr] = holds;
}

std::optional<bool> TypeRefCompares::TypeRefCompareIn(
    const Expr* expr, const std::string& scope) const {
  auto unit = unit_type_ref_compares_.find(expr);
  if (unit != unit_type_ref_compares_.end()) return unit->second;
  auto by_scope = type_ref_compares_.find(expr);
  if (by_scope == type_ref_compares_.end()) return std::nullopt;
  auto found = by_scope->second.find(scope);
  if (found == by_scope->second.end()) return std::nullopt;
  return found->second;
}

std::optional<bool> SimContext::TypeRefCompareHere(const Expr* expr) const {
  std::string scope = ActiveInstancePrefix();
  if (current_process_ != nullptr) {
    scope += ActiveGenBlockPrefix();
  } else {
    scope += LoweringGenBlockPrefix();
  }
  return TypeRefCompareIn(expr, scope);
}

std::string_view SimContext::GenBlockPrefixOf(const Process& proc) {
  const std::vector<FrameOwnerEntry>& owners = proc.frame_owners;
  const std::vector<std::string>& blocks = proc.gen_prefixes;
  const size_t kDepth = owners.empty()
                            ? blocks.size()
                            : std::min(owners.back().gen_depth, blocks.size());
  if (kDepth == 0) return {};
  return blocks[kDepth - 1];
}

void SimContext::PushStaticScope(std::string_view func_name) {
  scope_stack_.push_back(Scope{static_frames_[StaticFrameKey(func_name)],
                               {},
                               {},
                               {},
                               {},
                               {},
                               false,
                               {},
                               {},
                               stmt_frame_names_.contains(func_name.data())
                                   ? func_name
                                   : std::string_view{}});
}

void SimContext::PopStaticScope(std::string_view func_name) {
  if (!scope_stack_.empty()) {
    static_frames_[StaticFrameKey(func_name)] = scope_stack_.back().vars;
    scope_stack_.pop_back();
  }
}

std::vector<Scope>::const_reverse_iterator ScopeStack::VisibleFramesEnd()
    const {
  for (auto it = scope_stack_.crbegin(); it != scope_stack_.crend(); ++it) {
    if (it->is_subroutine) return std::next(it);
  }
  return scope_stack_.crend();
}

Variable* ScopeStack::FindLocalVariable(std::string_view name) {
  for (auto it = scope_stack_.crbegin(); it != VisibleFramesEnd(); ++it) {
    auto found = it->vars.find(name);
    if (found != it->vars.end()) return found->second;
  }
  return nullptr;
}

void ScopeStack::DeclareLocalLet(std::string_view name, ModuleItem* let) {
  scope_stack_.back().lets[name] = let;
}

ModuleItem* ScopeStack::FindLocalLet(std::string_view name) const {
  for (auto it = scope_stack_.crbegin(); it != VisibleFramesEnd(); ++it) {
    auto found = it->lets.find(name);
    if (found != it->lets.end()) return found->second;
  }
  return nullptr;
}

bool ScopeStack::InnermostScopeDeclares(std::string_view name) const {
  return !scope_stack_.empty() && scope_stack_.back().vars.contains(name);
}

void SimContext::PushActiveNamedScope(std::string_view name) {
  active_scope_stack_.push_back(name);
}

const std::vector<std::string_view>& SimContext::ActiveNamedScopes() const {
  return active_scope_stack_;
}

Variable* SimContext::CreateLocalVariable(std::string_view name, uint32_t width,
                                          bool is_signed) {
  auto* var = arena_.Create<Variable>();
  var->value = MakeLogic4VecVal(arena_, width, 0);
  var->is_signed = is_signed;
  var->value.is_signed = is_signed;
  if (!scope_stack_.empty()) {
    scope_stack_.back().vars[name] = var;
  }
  return var;
}

Variable* SimContext::FindStaticFuncVar(std::string_view func_name,
                                        std::string_view var_name) {
  auto it = static_frames_.find(StaticFrameKey(func_name));
  if (it == static_frames_.end()) return nullptr;
  auto vit = it->second.find(var_name);
  if (vit == it->second.end()) return nullptr;
  return vit->second;
}

void SimContext::SaveStaticFuncVar(std::string_view func_name,
                                   std::string_view var_name, Variable* var) {
  static_frames_[StaticFrameKey(func_name)][var_name] = var;
}

void ScopeStack::AliasLocalVariable(std::string_view name, Variable* var) {
  if (!scope_stack_.empty()) {
    scope_stack_.back().vars[name] = var;
  }
}

void ScopeStack::PushFuncName(std::string_view name) {
  func_name_stack_.push_back(name);
}

void ScopeStack::PopFuncName() {
  if (!func_name_stack_.empty()) func_name_stack_.pop_back();
}

std::string_view ScopeStack::CurrentFuncName() const {
  return func_name_stack_.empty() ? std::string_view{}
                                  : func_name_stack_.back();
}

std::string_view ScopeStack::StmtFrameName(const Stmt* stmt) {
  auto [it, inserted] = stmt_frames_.try_emplace(stmt);
  if (inserted) {
    const SourceLoc& at = stmt->range.start;
    std::string_view label = stmt->label.empty() ? "block" : stmt->label;
    it->second =
        std::format("{}@{}:{}:{}", label, at.file_id, at.line, at.column);
    stmt_frame_names_.insert(it->second.data());
  }
  return it->second;
}

std::string_view ScopeStack::InnermostStmtFrame() const {
  return scope_stack_.empty() ? std::string_view{}
                              : scope_stack_.back().stmt_frame;
}

}  // namespace delta
