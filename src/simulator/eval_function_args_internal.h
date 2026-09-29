#pragma once

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "common/types.h"
#include "simulator/eval_class_sync.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"

namespace delta {

struct ArrayInfo;
struct ClassArrayRef;
struct ClassObject;
struct ClassTypeInfo;
struct DataType;
struct Expr;
struct FunctionArg;
struct ModuleItem;
class Arena;

// The helpers the argument binding of eval_function_args.cpp shares with the
// binds split out beside it (eval_function_args_array.cpp and
// eval_function_args_sync.cpp).

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

// The position `k`, counted from the left, of the one-dimensional array
// `info` as an address: `[4:1]` puts position 0 at 4, `[1:4]` at 1. §7.6
// (printed page 160) pairs two arrays' elements left to right, which is how
// §7.7 (printed 162) passes an array of another range. Defined in
// eval_function_args_array.cpp.
uint32_t ElementIndexAt(const ArrayInfo& info, uint32_t k);

// §7.4.2 with §7.6 (printed pages 153 and 160): how many elements the fixed-
// size array `info` holds across all its unpacked dimensions, and the address
// suffix, `[i]` or `[i0][i1]...`, of the one at row-major position `k`, each
// dimension counted from its left bound. Two arrays of the same sizes pair
// their elements at equal positions whatever their ranges, which is how §7.7
// (printed 162) passes a multidimensional array. Defined in
// eval_function_args_array.cpp.
uint32_t ArrayElementCount(const ArrayInfo& info);
std::string ArrayElementSuffixAt(const ArrayInfo& info, uint32_t k);

// §7.4.2 with §7.5: the shape of the fixed or dynamic array property `ref`
// addresses, a dynamic one counting from 0 up. Defined in
// eval_function_args_array.cpp.
ArrayInfo ClassArrayShape(const ClassArrayRef& ref);

// §7.7 (printed page 162): binds `formal` by value to the array the actual
// `call_arg` names -- an associative array, a dynamic array or queue, or a
// fixed-size array, declared or a property reached through a handle -- as a
// copy of it in the callee's scope. False, binding nothing, where the actual
// names no array. Defined in eval_function_args_array.cpp.
bool TryBindArrayArg(const Expr* call_arg, const FunctionArg& formal,
                     SimContext& ctx, Arena& arena);

// §13.5.2 with §8.5: the object and the key of the instance property, or of
// the element of an instance array property, that the ref actual `actual`
// names through a handle -- `c.k`, `this.k`, `c.arr[i]` -- read in the
// running scope; false for any other actual, a static property among them.
// Defined in eval_function_args_array.cpp.
bool RefPropertyTarget(const Expr* actual, SimContext& ctx, Arena& arena,
                       ClassObject*& obj, std::string& key);

// §13.3 with §6.21 and §6.8 (Table 6-7): the value an output formal of
// `type`, `width` bits wide, starts at on entry to an automatic subroutine,
// which is what it copies out if the body never writes it: x for a 4-state
// integral type, 0 for any other. Defined in eval_function_args_array.cpp.
Logic4Vec OutputFormalDefault(const DataType& type, uint32_t width,
                              const SimContext& ctx, Arena& arena);

// §13.3.2 (printed page 339): the formals of a static subroutine `func`,
// "including input, output, and inout type arguments", "retain their values
// between invocations". An array formal TryBindArrayArg bound is kept as the
// subroutine's static storage (RetainStaticAggregate), its element variables
// in the static frame; an output formal, into which the call copies nothing,
// refers to what the last call left instead of the default it was bound at.
// Nothing for an automatic subroutine. Defined in
// eval_function_args_array.cpp.
void KeepStaticArrayFormal(const ModuleItem* func, const FunctionArg& formal,
                           SimContext& ctx, Arena& arena);

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
