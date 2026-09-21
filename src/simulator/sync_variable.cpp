#include "simulator/sync_variable.h"

#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "simulator/eval_mailbox.h"
#include "simulator/eval_semaphore.h"
#include "simulator/sim_context.h"
#include "simulator/sync_objects.h"
#include "simulator/variable.h"

namespace delta {

// §8.4 (printed page 182 of IEEE 1800-2023): the value the variable holds
// while its handle refers to an object is the object's identity
// (SyncObjectIdentity), as MirrorSyncCarrier (eval_class_sync.cpp) stores a
// property's, at the variable's own width; the null handle is the 0 the
// declaration stored. Stored as a 1 for every object, two variables each
// built by its own `new` compared equal.
static void MarkSyncVariableHeld(Variable* v, const void* obj, Arena& arena) {
  v->value = MakeLogic4VecVal(arena, v->value.width, SyncObjectIdentity(obj));
}

// §15.3.1 and §15.4.1: whether the declaration's initializer is the
// `new(...)` call that creates the object and returns its handle.
static bool InitIsNew(const RtlirVariable& var) {
  return var.init_expr != nullptr && var.init_expr->kind == ExprKind::kCall &&
         var.init_expr->text == "new";
}

// §15.3: a semaphore is a bucket of keys, made under the variable's name.
// §15.3.1's new() sets how many keys are in it and defaults that to none,
// so a bucket no new() has reached yet is empty and every get() on it
// waits.
static void CreateSemaphoreForVar(std::string_view name,
                                  const RtlirVariable& var, Variable* v,
                                  SimContext& ctx, Arena& arena) {
  auto* sem = ctx.CreateSemaphore(name, 0);
  if (!InitIsNew(var)) return;
  sem->key_count = SemaphoreKeyArg(var.init_expr, ctx, arena, 0);
  MarkSyncVariableHeld(v, sem, arena);
}

// §15.4: a mailbox is a queue messages pass through between processes, made
// under the variable's name. §15.4.1's new() sets its bound, 0 leaving it
// unbounded, so a queue no new() has reached yet takes messages without
// limit and every get() on it waits until one is placed.
static void CreateMailboxForVar(std::string_view name, const RtlirVariable& var,
                                Variable* v, SimContext& ctx, Arena& arena) {
  auto* mbx = ctx.CreateMailbox(name, 0);
  if (!InitIsNew(var)) return;
  mbx->Build(MailboxBoundArg(var.init_expr, ctx, arena));
  MarkSyncVariableHeld(v, mbx, arena);
}

// The variable's value was left at the 0 the declaration stored whether or
// not its `= new` had built the object, so `mailbox mb = new;` compared
// equal to null as `mailbox mb;` did; the declaration's new() now marks the
// handle held, and a procedural one HoldSyncVariable.
void CreateSyncObjectForVar(std::string_view name, const RtlirVariable& var,
                            Variable* v, SimContext& ctx, Arena& arena) {
  if (var.class_type_name == "semaphore") {
    CreateSemaphoreForVar(name, var, v, ctx, arena);
  } else if (var.class_type_name == "mailbox") {
    CreateMailboxForVar(name, var, v, ctx, arena);
  }
}

void HoldSyncVariable(std::string_view key, SimContext& ctx) {
  Variable* v = ctx.FindVariable(key);
  if (v == nullptr) return;
  const void* obj = ctx.FindSemaphore(key);
  if (obj == nullptr) obj = ctx.FindMailbox(key);
  MarkSyncVariableHeld(v, obj, ctx.GetArena());
}

}  // namespace delta
