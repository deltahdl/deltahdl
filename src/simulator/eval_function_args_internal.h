#pragma once

#include <cstdint>
#include <string>
#include <utility>

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

bool& CalleeOwnsThisFlag();

inline bool& CalleeOwnsClassFlag() {
  static thread_local bool flag = false;
  return flag;
}

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

class CalleeScopeAside {
 public:
  explicit CalleeScopeAside(SimContext& ctx) : ctx_(ctx) {
    if (ctx_.HasLocalScope()) {
      callee_ = ctx_.DetachScope();
      set_aside_ = true;
    }
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
    if (set_aside_) ctx_.RestoreScope(std::move(callee_));
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

uint32_t ElementIndexAt(const ArrayInfo& info, uint32_t k);

uint32_t ArrayElementCount(const ArrayInfo& info);
std::string ArrayElementSuffixAt(const ArrayInfo& info, uint32_t k);

ArrayInfo ClassArrayShape(const ClassArrayRef& ref);

bool TryBindArrayArg(const Expr* call_arg, const FunctionArg& formal,
                     SimContext& ctx, Arena& arena);

bool RefPropertyTarget(const Expr* actual, SimContext& ctx, Arena& arena,
                       ClassObject*& obj, std::string& key);

Logic4Vec OutputFormalDefault(const DataType& type, uint32_t width,
                              const SimContext& ctx, Arena& arena);

void KeepStaticArrayFormal(const ModuleItem* func, const FunctionArg& formal,
                           SimContext& ctx, Arena& arena);

SyncHandle SyncActualOf(const FunctionArg& param, const Expr* actual,
                        const ModuleItem* func, SimContext& ctx, Arena& arena);

void BindRefSyncFormal(const FunctionArg& param, const Expr* actual,
                       const ModuleItem* func, SimContext& ctx, Arena& arena);

bool TryBindEventFormal(const Expr* call, int arg_index,
                        const FunctionArg& param, SimContext& ctx);

}  // namespace delta
