#pragma once

#include <string_view>
#include <unordered_map>
#include <vector>

#include "simulator/scope.h"

namespace delta {

struct DataType;
struct Variable;

// §23.9 (printed page 761): the scope stack one simulation run keeps for the
// subroutine bodies and the blocks a process is running -- pushing and
// marking a frame, what a frame binds, the walk a bare name is looked up by
// -- and the stack of subroutine names beside it. A base class of
// SimContext, as simulator/sim_context_random_stability.h's is, so that every
// call through a SimContext reads as it did; SimContext itself keeps the
// operations that need its arena or its running process, a static
// function's retained frame among them, and reaches the stack as a protected
// member. Defined in sim_context_scope.cpp.
class ScopeStack {
 public:
  // `package` is Scope::package, the package a subroutine the scope belongs
  // to was declared in, empty for every other scope.
  void PushScope(std::string_view package = {});
  // §23.9 with §26.2: marks the innermost frame a subroutine body's and gives
  // it the package its bare names are read from, none for an empty name.
  void EnterSubroutineScope(std::string_view package);
  void PopScope();
  std::vector<Scope> SwapScopeStack(std::vector<Scope> new_stack);
  bool HasLocalScope() const { return !scope_stack_.empty(); }
  // §23.9: the end of the frames a bare name is looked up in, walking the
  // stack inward from crbegin(): the frames down to and including the
  // innermost subroutine frame, since a task's or function's body is a scope
  // nested in the module, package or class declaring it, and the caller's
  // body, another branch of the name tree, is not searched.
  std::vector<Scope>::const_reverse_iterator VisibleFramesEnd() const;
  Variable* FindLocalVariable(std::string_view name);
  // §26.3 with §23.9: the innermost frame naming a package, or null where
  // the innermost subroutine frame is reached first.
  const Scope* PackageFrame() const;
  // Makes `var`, a variable created earlier, the variable `name` names in
  // the innermost scope, as SimContext::CreateLocalVariable makes the one it
  // creates: what a constraint's trial does with the locals it binds the
  // random variables to, which it makes once per randomize() call and binds
  // once per relation it evaluates (18.5). The caller must have pushed a
  // scope, and `name` must outlive it.
  void BindLocalVariable(std::string_view name, Variable* var);
  void AliasLocalVariable(std::string_view name, Variable* var);
  // §8.25.1: binds, in the innermost scope, the type the specialization a
  // class-scope call names gives the type parameter `name`; the second reads
  // it back from the innermost scope binding the name, null where none does.
  void BindScopeTypeActual(std::string_view name, const DataType* actual);
  const DataType* FindScopeTypeActual(std::string_view name) const;

  void PushFuncName(std::string_view name);
  void PopFuncName();
  std::string_view CurrentFuncName() const;
  // The active subroutine call chain, outermost frame first. Used to report the
  // call stack for $stacktrace (§20.17.2).
  const std::vector<std::string_view>& FuncNameStack() const {
    return func_name_stack_;
  }

 protected:
  std::vector<Scope> scope_stack_;
  // §13.4.2: the variables of each static function's frame, kept between
  // calls under SimContext::StaticFrameKey.
  std::unordered_map<std::string_view,
                     std::unordered_map<std::string_view, Variable*>>
      static_frames_;
  std::vector<std::string_view> func_name_stack_;
};

}  // namespace delta
