#include <cstdint>
#include <iterator>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/process.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_scope_stack.h"
#include "simulator/variable.h"

namespace delta {

// §23.9 (printed page 761): the scope stack SimContext keeps for the
// subroutine bodies and the blocks a process is running -- pushing and
// marking a frame, the variables and type actuals a frame binds, the walk
// a bare name is looked up by, a static subroutine's retained frame and the
// stack of subroutine names -- kept apart from sim_context.cpp, which had
// grown past the line cap.

void ScopeStack::PushScope(std::string_view package) {
  scope_stack_.push_back(Scope{{}, {}, {}, {}, package, {}, false, {}});
}

// §23.9 with §26.2: the innermost frame -- a subroutine's, pushed by the
// caller before the actuals are bound -- becomes the frame PackageFrame
// stops at, and is given the package whose names the body reads by their
// bare names, none for an empty name. Both are set once the actuals are in
// place, so that a caller's actual spelt like a package variable still reads
// the caller's, its own import included.
void ScopeStack::EnterSubroutineScope(std::string_view package) {
  if (scope_stack_.empty()) return;
  scope_stack_.back().is_subroutine = true;
  if (!package.empty()) scope_stack_.back().package = package;
}

// §26.3 with §13.3: a task's frame is pushed by PushTaskCallScope
// (eval_function.cpp) with no package and the actuals are bound into it in
// the caller's scope, so the package whose names the body reads bare -- the
// task's own, or the key its body imports are recorded under
// (LowerSubroutineBodyImports in lowerer_import.cpp) -- is set once
// SetupTaskCall has bound them, which is why ExecInlineTaskCall
// (stmt_exec.cpp) passes its result through here; a function's frame is
// given it by EvalFunctionCall before its default actuals are read.
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

// §26.3 with §23.9: the frame whose package a bare name is read through is
// the innermost one naming a package -- a package subroutine's own, or the
// key a module subroutine's body imports are recorded under
// (LowerSubroutineBodyImports in lowerer_import.cpp) -- and the search ends
// at the innermost subroutine frame, since a subroutine's body is a scope
// nested in the module or package declaring it and not in its caller's body.
// A block, fork or loop frame inside the body is walked past to the body's
// own frame; a callee whose frame names no package sees none of its
// caller's, where walking on had it read the caller's import. Null where no
// frame supplies a package, a module process's block frames included.
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

std::vector<Scope> ScopeStack::SwapScopeStack(std::vector<Scope> new_stack) {
  auto old = std::move(scope_stack_);
  scope_stack_ = std::move(new_stack);
  return old;
}

std::string_view SimContext::StaticFrameKey(std::string_view name) {
  if (!current_process_ || current_process_->inst_prefix.empty()) return name;
  auto* key = arena_.Create<std::string>(current_process_->inst_prefix +
                                         std::string(name));
  return *key;
}

void SimContext::PushStaticScope(std::string_view func_name) {
  // §13.4.2's static frame carries the variables the function declared static;
  // the three maps beside them start empty, a queue or associative array of the
  // call being the call's own and a shape with it.
  scope_stack_.push_back(Scope{static_frames_[StaticFrameKey(func_name)],
                               {},
                               {},
                               {},
                               {},
                               {},
                               false,
                               {}});
}

void SimContext::PopStaticScope(std::string_view func_name) {
  if (!scope_stack_.empty()) {
    static_frames_[StaticFrameKey(func_name)] = scope_stack_.back().vars;
    scope_stack_.pop_back();
  }
}

// §23.9 (printed page 761): a name referenced directly within a task or
// function is declared in it or in a scope higher in the same branch of the
// name tree, so the frames its body sees end at the body's own frame, the
// innermost one EnterSubroutineScope marked; a begin-end, fork or loop frame
// inside the body is walked past to it, and a module process's block frames,
// under no subroutine, are all visible. Walked to the bottom of the stack,
// every lookup below read the callers' locals as the callee's own:
// uvm_coreservice_t::set(cs), its `inst = cs` run under a caller holding a
// local named inst, stored the handle in that local, and
// uvm_coreservice_t::get() on the next call found the class's inst null.
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

Variable* SimContext::CreateLocalVariable(std::string_view name, uint32_t width,
                                          bool is_signed) {
  auto* var = arena_.Create<Variable>();
  var->value = MakeLogic4VecVal(arena_, width, 0);
  // The declaration's signedness belongs both to the object and to the value
  // standing in it: reads go through the variable's flag, while a value taken
  // straight out of the cell carries its own.
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

}  // namespace delta
