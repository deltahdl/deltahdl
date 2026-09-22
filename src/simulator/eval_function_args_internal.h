#pragma once

#include <utility>
#include <vector>

#include "simulator/eval_class_sync.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"

namespace delta {

struct ClassObject;
struct ClassTypeInfo;
struct Expr;
struct FunctionArg;
struct ModuleItem;
class Arena;

// The helpers the argument binding of eval_function_args.cpp shares with the
// binds split out beside it (eval_function_args_sync.cpp).

// Whether the object on top of the `this` stack is the callee's own, pushed
// for the call being bound rather than the caller's; BindFunctionArgs
// decides it (CalleeOwnsThis) and holds it for the reads of the actuals.
// Defined in eval_function_args.cpp.
bool& CalleeOwnsThisFlag();

// Whether the class on top of the method-class stack is the callee's own,
// pushed for the call being bound with no object beside it: §8.10 (printed
// page 186) runs a static method in its class's scope with no `this`, and
// every call of one -- `C::m(...)`, `C#(P)::m(...)`, `h.m(...)`, a bare
// call from within the class, and the static task alike -- pushes that class
// before the actuals are bound. BindFunctionArgs holds it for the reads of
// the actuals (CalleeOwnsClassScope).
inline bool& CalleeOwnsClassFlag() {
  static thread_local bool flag = false;
  return flag;
}

// Holds CalleeOwnsClassFlag at `owns` for one binding and restores the
// enclosing binding's on the way out, as CalleeOwnsThisScope does its flag.
class CalleeOwnsClassScope {
 public:
  explicit CalleeOwnsClassScope(bool owns) : previous_(CalleeOwnsClassFlag()) {
    CalleeOwnsClassFlag() = owns;
  }
  ~CalleeOwnsClassScope() { CalleeOwnsClassFlag() = previous_; }
  CalleeOwnsClassScope(const CalleeOwnsClassScope&) = delete;
  CalleeOwnsClassScope& operator=(const CalleeOwnsClassScope&) = delete;

 private:
  bool previous_;
};

// §13.5: an actual argument is an expression of the caller, read before the
// subroutine's formals exist. BindFunctionArgs runs after the callee's scope
// is pushed, and for a static subroutine §13.3.2 has that scope carry the
// formals of the last call, so an actual named after a formal read the formal:
// error_type(opcode) with `input int opcode` refreshed the formal from itself
// and never saw the caller's opcode change, and an actual named after a formal
// bound just before it read that formal instead of the caller's variable.
// While one of these lives the callee's scope is set aside and the caller's
// stands on top; it is put back when the object goes, so the binding that
// follows the read still lands in the callee's scope.
//
// The callee's object is set aside with its scope. §8.11 (printed page 187)
// makes a property named inside a method, bare or through `this`, the
// property of the object the method was invoked on, and the actual is
// written inside the caller's method: `b.add8(v)` in a method of A names
// A's `v`. ExecInstanceMethodCall and SetupInstanceTaskCall push the
// callee's object, and the class defining the method with it, before the
// actuals are bound, so `v` was looked up on B's object, which has none, and
// add8 was passed 0. Which binding this holds for is what BindFunctionArgs
// decides (CalleeOwnsThis) and records for the reads of the actuals.
//
// A static method's class is set aside alone, the caller's object staying in
// force. §8.23 (printed page 200) has the class a scope names looked up where
// the call is written, so `C::chk(T::get())` in `H #(type T)` names H's T,
// and `C::twice(n)` in a static method of A names A's static n: read under
// C, the first found no T and passed the null handle, and the second read
// C's own n.
class CalleeScopeAside {
 public:
  explicit CalleeScopeAside(SimContext& ctx) : ctx_(ctx) {
    std::vector<Scope> stack = ctx_.SwapScopeStack({});
    if (!stack.empty()) {
      callee_ = std::move(stack.back());
      stack.pop_back();
      set_aside_ = true;
    }
    ctx_.SwapScopeStack(std::move(stack));
    if (CalleeOwnsClassFlag()) {
      method_class_ = ctx_.CurrentMethodClass();
      ctx_.PopMethodClass();
      class_set_aside_ = true;
    }
    if (!CalleeOwnsThisFlag()) return;
    self_ = ctx_.CurrentThis();
    method_class_ = ctx_.CurrentMethodClass();
    ctx_.PopThis();
    ctx_.PopMethodClass();
    this_set_aside_ = true;
  }
  ~CalleeScopeAside() {
    if (class_set_aside_) ctx_.PushMethodClass(method_class_);
    if (this_set_aside_) {
      ctx_.PushMethodClass(method_class_);
      ctx_.PushThis(self_);
    }
    if (!set_aside_) return;
    std::vector<Scope> stack = ctx_.SwapScopeStack({});
    stack.push_back(std::move(callee_));
    ctx_.SwapScopeStack(std::move(stack));
  }
  CalleeScopeAside(const CalleeScopeAside&) = delete;
  CalleeScopeAside& operator=(const CalleeScopeAside&) = delete;

 private:
  SimContext& ctx_;
  Scope callee_;
  bool set_aside_ = false;
  ClassObject* self_ = nullptr;
  const ClassTypeInfo* method_class_ = nullptr;
  bool this_set_aside_ = false;
  bool class_set_aside_ = false;
};

// §13.5.1 (printed page 348) with §8.2 (printed 180): an object passed by
// value is passed as its handle, so the actual of a `mailbox m` or
// `semaphore s` formal of the subroutine `func` is read for the object it is
// a handle to, in the caller's scope; `actual` is the call's expression for
// the formal, or null where the call passes none. Of kind kNone, binding
// nothing, for a formal of any other type. Defined in
// eval_function_args_sync.cpp.
SyncHandle SyncActualOf(const FunctionArg& param, const Expr* actual,
                        const ModuleItem* func, SimContext& ctx, Arena& arena);

}  // namespace delta
