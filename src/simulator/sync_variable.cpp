#include "simulator/sync_variable.h"

#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/covergroup_instance.h"
#include "simulator/eval_class_sync.h"
#include "simulator/eval_mailbox.h"
#include "simulator/eval_semaphore.h"
#include "simulator/sim_context.h"
#include "simulator/sync_objects.h"
#include "simulator/variable.h"

namespace delta {

static void MarkSyncVariableHeld(Variable* v, const void* obj, Arena& arena) {
  v->value = MakeLogic4VecVal(arena, v->value.width, SyncObjectIdentity(obj));
}

static bool InitIsNew(const RtlirVariable& var) {
  return var.init_expr != nullptr && var.init_expr->kind == ExprKind::kCall &&
         var.init_expr->text == "new";
}

static void CreateSemaphoreForVar(std::string_view name,
                                  const RtlirVariable& var, Variable* v,
                                  SimContext& ctx, Arena& arena) {
  auto* sem = ctx.CreateSemaphore(name, 0);
  if (!InitIsNew(var)) return;
  sem->key_count = SemaphoreKeyArg(var.init_expr, ctx, arena, 0);
  MarkSyncVariableHeld(v, sem, arena);
}

static void CreateMailboxForVar(std::string_view name, const RtlirVariable& var,
                                Variable* v, SimContext& ctx, Arena& arena) {
  auto* mbx = ctx.CreateMailbox(name, 0);
  if (!InitIsNew(var)) return;
  mbx->Build(MailboxBoundArg(var.init_expr, ctx, arena));
  MarkSyncVariableHeld(v, mbx, arena);
}

void CreateSyncObjectForVar(std::string_view name, const RtlirVariable& var,
                            Variable* v, SimContext& ctx, Arena& arena) {
  SyncKind kind = BuiltinSyncKindOf(var.class_type_name, ctx);
  if (kind == SyncKind::kSemaphore) {
    CreateSemaphoreForVar(name, var, v, ctx, arena);
  } else if (kind == SyncKind::kMailbox) {
    CreateMailboxForVar(name, var, v, ctx, arena);
  } else if (var.covergroup != nullptr) {
    CreateCovergroupForVar(name, var, v, ctx, arena);
  }
}

void HoldSyncVariable(std::string_view key, SimContext& ctx) {
  Variable* v = ctx.FindVariable(key);
  if (v == nullptr) return;
  const void* obj = ctx.FindSemaphore(key);
  if (obj == nullptr) obj = ctx.FindMailbox(key);
  MarkSyncVariableHeld(v, obj, ctx.GetArena());
}

static bool IsNewCall(const Expr* e) {
  return e != nullptr && e->kind == ExprKind::kCall && e->text == "new";
}

static void BindNewLocalSyncObject(SyncKind kind, const Expr* new_expr,
                                   Variable* v, SimContext& ctx, Arena& arena) {
  bool is_new = IsNewCall(new_expr);
  const void* obj = nullptr;
  if (kind == SyncKind::kSemaphore) {
    auto* sem = ctx.GetArena().Create<SemaphoreObject>(
        is_new ? SemaphoreKeyArg(new_expr, ctx, arena, 0) : 0);
    ctx.BindSemaphoreHandle(v, sem);
    obj = sem;
  } else {
    auto* mbx = ctx.GetArena().Create<MailboxObject>();
    if (is_new) mbx->Build(MailboxBoundArg(new_expr, ctx, arena));
    ctx.BindMailboxHandle(v, mbx);
    obj = mbx;
  }
  MarkSyncVariableHeld(v, is_new ? obj : nullptr, arena);
}

void CreateSyncObjectForLocal(const Stmt* stmt, Variable* v, SimContext& ctx,
                              Arena& arena) {
  if (v == nullptr || !stmt->var_unpacked_dims.empty()) return;
  SyncKind kind = SyncKindOfType(stmt->var_decl_type, ctx);
  if (kind == SyncKind::kNone) return;
  BindNewLocalSyncObject(kind, stmt->var_init, v, ctx, arena);
}

bool TryLocalSyncNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->lhs == nullptr || stmt->lhs->kind != ExprKind::kIdentifier ||
      !IsNewCall(stmt->rhs)) {
    return false;
  }
  Variable* v = ctx.FindLocalVariable(stmt->lhs->text);
  if (v == nullptr) return false;
  if (ctx.SemaphoreOfHandle(v) != nullptr) {
    BindNewLocalSyncObject(SyncKind::kSemaphore, stmt->rhs, v, ctx, arena);
  } else if (ctx.MailboxOfHandle(v) != nullptr) {
    BindNewLocalSyncObject(SyncKind::kMailbox, stmt->rhs, v, ctx, arena);
  } else {
    return false;
  }
  return true;
}

}  // namespace delta
