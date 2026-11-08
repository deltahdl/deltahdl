#include "simulator/eval_class_sync.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_mailbox.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sync_objects.h"

namespace delta {

static std::string_view TypeTargetFor(std::string_view name,
                                      std::string_view package,
                                      const SimContext& ctx) {
  if (!package.empty() && name.find("::") == std::string_view::npos) {
    std::string_view target =
        ctx.FindTypeTarget(std::string(package) + "::" + std::string(name));
    if (!target.empty()) return target;
  }
  return ctx.FindTypeTarget(name);
}

SyncKind BuiltinSyncKindOf(std::string_view name, const SimContext& ctx) {
  constexpr std::string_view kStdScope = "std::";
  const bool kStdScoped = name.starts_with(kStdScope);
  if (kStdScoped) name.remove_prefix(kStdScope.size());
  SyncKind kind = SyncKind::kNone;
  if (name == "semaphore") kind = SyncKind::kSemaphore;
  if (name == "mailbox") kind = SyncKind::kMailbox;
  if (kind == SyncKind::kNone ||
      (!kStdScoped && ctx.FindClassType(name) != nullptr))
    return SyncKind::kNone;
  return kind;
}

SyncKind SyncKindOfType(const DataType& type, std::string_view package,
                        const SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed) return SyncKind::kNone;
  std::string name =
      type.scope_name.empty()
          ? std::string(type.type_name)
          : std::string(type.scope_name) + "::" + std::string(type.type_name);
  for (size_t steps = 0; steps <= ctx.TypeTargetCount(); ++steps) {
    SyncKind kind = BuiltinSyncKindOf(name, ctx);
    if (kind != SyncKind::kNone) return kind;
    std::string_view target = TypeTargetFor(name, package, ctx);
    if (target.empty()) return SyncKind::kNone;
    name = std::string(target);
  }
  return SyncKind::kNone;
}

SyncKind SyncKindOfType(const DataType& type, const SimContext& ctx) {
  return SyncKindOfType(type, {}, ctx);
}

struct SyncMember {
  const ClassMember* member = nullptr;
  const ClassTypeInfo* declaring = nullptr;
};

static SyncMember NearestPropertyDecl(const ClassTypeInfo* from,
                                      std::string_view name) {
  for (const ClassTypeInfo* t = from; t != nullptr; t = t->parent) {
    if (t->decl == nullptr) continue;
    for (const ClassMember* m : t->decl->members) {
      if (m->kind == ClassMemberKind::kProperty && m->name == name)
        return {m, t};
    }
  }
  return {};
}

static SyncKind SyncKindOfMember(const SyncMember& m, const SimContext& ctx) {
  return SyncKindOfType(m.member->data_type, m.declaring->package, ctx);
}

static bool IsSyncMember(const SyncMember& m, const SimContext& ctx) {
  return m.member != nullptr && !m.member->is_param &&
         m.member->unpacked_dims.empty() &&
         SyncKindOfMember(m, ctx) != SyncKind::kNone;
}

static SyncMember SyncPropertyMember(const ClassTypeInfo* from,
                                     std::string_view name,
                                     const SimContext& ctx) {
  SyncMember nearest = NearestPropertyDecl(from, name);
  return IsSyncMember(nearest, ctx) ? nearest : SyncMember{};
}

static SyncMember EnclosingStaticSyncMember(const ClassTypeInfo* from,
                                            std::string_view name,
                                            const SimContext& ctx) {
  for (const ClassTypeInfo* t = from->enclosing; t != nullptr;
       t = t->enclosing) {
    SyncMember nearest = NearestPropertyDecl(t, name);
    if (nearest.member == nullptr) continue;
    bool is_static_sync =
        nearest.member->is_static && IsSyncMember(nearest, ctx);
    return is_static_sync ? nearest : SyncMember{};
  }
  return {};
}

static SyncProperty MakeSyncProperty(const SyncMember& m, ClassObject* obj,
                                     std::string spelling,
                                     const SimContext& ctx) {
  return {SyncKindOfMember(m, ctx), obj, m.member, m.declaring,
          std::move(spelling)};
}

static std::string SpellHandlePath(const Expr* expr) {
  if (expr->kind == ExprKind::kIdentifier) return std::string(expr->text);
  if (expr->kind == ExprKind::kCall) return std::string(expr->callee) + "()";
  return SpellHandlePath(expr->lhs) + (expr->is_scope_resolution ? "::" : ".") +
         std::string(expr->rhs->text);
}

static SyncProperty ResolveBareSyncProperty(std::string_view name,
                                            SimContext& ctx) {
  ClassObject* self = ctx.CurrentThis();
  const ClassTypeInfo* from = ctx.CurrentMethodClass();
  if (from == nullptr && self != nullptr) from = self->type;
  if (from == nullptr || ctx.FindLocalVariable(name) != nullptr) return {};
  SyncMember member = NearestPropertyDecl(from, name).member == nullptr
                          ? EnclosingStaticSyncMember(from, name, ctx)
                          : SyncPropertyMember(from, name, ctx);
  if (member.member == nullptr) return {};
  return MakeSyncProperty(member, self, std::string(name), ctx);
}

static const ClassTypeInfo* DeclaredClassOfHandleSide(const Expr* side,
                                                      SimContext& ctx) {
  if (side->kind != ExprKind::kIdentifier) return nullptr;
  if (side->text == "this") return ctx.CurrentMethodClass();
  std::string_view class_name = ctx.GetVariableClassType(side->text);
  if (class_name.empty() && ctx.CurrentMethodClass() != nullptr) {
    class_name = PropertyClassName(ctx.CurrentThis(), ctx.CurrentMethodClass(),
                                   side->text, ctx);
  }
  return class_name.empty() ? nullptr : ctx.FindClassType(class_name);
}

static SyncProperty ResolveSyncPropertyThroughHandle(const Expr* recv,
                                                     SimContext& ctx,
                                                     Arena& arena) {
  std::string_view name = recv->rhs->text;
  if (ClassObject* obj = HandleSideObject(recv->lhs, ctx, arena)) {
    SyncMember member = SyncPropertyMember(obj->type, name, ctx);
    if (member.member == nullptr) return {};
    return MakeSyncProperty(member, obj, SpellHandlePath(recv), ctx);
  }
  const ClassTypeInfo* cls = DeclaredClassOfHandleSide(recv->lhs, ctx);
  SyncMember member =
      cls != nullptr ? SyncPropertyMember(cls, name, ctx) : SyncMember{};
  if (member.member == nullptr) return {};
  return MakeSyncProperty(member, nullptr, SpellHandlePath(recv->lhs), ctx);
}

static SyncProperty ResolveScopedSyncProperty(const Expr* recv,
                                              SimContext& ctx) {
  if (recv->lhs == nullptr || recv->lhs->kind != ExprKind::kIdentifier)
    return {};
  const ClassTypeInfo* cls = ctx.FindClassType(recv->lhs->text);
  if (cls == nullptr) return {};
  SyncMember member = SyncPropertyMember(cls, recv->rhs->text, ctx);
  if (member.member == nullptr || !member.member->is_static) return {};
  return MakeSyncProperty(member, nullptr, SpellHandlePath(recv), ctx);
}

SyncProperty ResolveSyncProperty(const Expr* recv, SimContext& ctx,
                                 Arena& arena) {
  if (recv == nullptr) return {};
  if (recv->kind == ExprKind::kIdentifier && recv->text != "this") {
    return ResolveBareSyncProperty(recv->text, ctx);
  }
  if (recv->kind != ExprKind::kMemberAccess || recv->rhs == nullptr ||
      recv->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  if (recv->is_scope_resolution) return ResolveScopedSyncProperty(recv, ctx);
  if (!IsHandlePath(recv->lhs)) return {};
  return ResolveSyncPropertyThroughHandle(recv, ctx, arena);
}

static void ReportNullSyncProperty(const SyncProperty& prop,
                                   std::string_view method, SourceLoc loc,
                                   SimContext& ctx) {
  if (!loc.IsValid()) return;
  ctx.GetDiag().Error(loc,
                      "method '" + std::string(method) +
                          "' called through the null handle '" + prop.spelling +
                          "'",
                      Subclause("8.4"));
}

static void MirrorSyncCarrier(const SyncProperty& prop, uint64_t identity,
                              SimContext& ctx) {
  std::string name(prop.member->name);
  Logic4Vec carrier = MakeLogic4VecVal(ctx.GetArena(), 64, identity);
  if (prop.member->is_static) {
    prop.declaring->static_properties[name] = carrier;
    return;
  }
  if (prop.obj == nullptr) return;
  std::string scoped = std::string(prop.declaring->name) + "::" + name;
  prop.obj->properties[scoped] = carrier;
  if (prop.obj->BareNameIsDeclaredBy(name, prop.declaring))
    prop.obj->properties[name] = carrier;
}

static std::unordered_map<std::string, SemaphoreObject*>* SemaphoreMapOf(
    const SyncProperty& prop) {
  if (prop.member->is_static)
    return &prop.declaring->static_semaphore_properties;
  return prop.obj == nullptr ? nullptr : &prop.obj->semaphore_properties;
}

static std::unordered_map<std::string, MailboxObject*>* MailboxMapOf(
    const SyncProperty& prop) {
  if (prop.member->is_static) return &prop.declaring->static_mailbox_properties;
  return prop.obj == nullptr ? nullptr : &prop.obj->mailbox_properties;
}

static bool HasStorage(const SyncProperty& prop) {
  return prop.member->is_static || prop.obj != nullptr;
}

static bool IsNewCall(const Expr* expr) {
  return expr != nullptr && expr->kind == ExprKind::kCall &&
         expr->text == "new";
}

template <typename T>
static T* HeldSyncObject(std::unordered_map<std::string, T*>* held,
                         const SyncProperty& prop) {
  if (held == nullptr) return nullptr;
  auto it = held->find(std::string(prop.member->name));
  return it != held->end() ? it->second : nullptr;
}

SemaphoreObject* SemaphoreOfProperty(const SyncProperty& prop,
                                     std::string_view method, SourceLoc loc,
                                     SimContext& ctx) {
  if (prop.kind != SyncKind::kSemaphore) return nullptr;
  SemaphoreObject* sem = HeldSyncObject(SemaphoreMapOf(prop), prop);
  if (sem == nullptr) ReportNullSyncProperty(prop, method, loc, ctx);
  return sem;
}

MailboxObject* MailboxOfProperty(const SyncProperty& prop,
                                 std::string_view method, SourceLoc loc,
                                 SimContext& ctx) {
  if (prop.kind != SyncKind::kMailbox) return nullptr;
  MailboxObject* mbx = HeldSyncObject(MailboxMapOf(prop), prop);
  if (mbx == nullptr) ReportNullSyncProperty(prop, method, loc, ctx);
  return mbx;
}

void BuildSyncProperty(const SyncProperty& prop, const Expr* new_expr,
                       SimContext& ctx, Arena& arena) {
  if (!HasStorage(prop)) {
    ReportNullSyncProperty(prop, "new", new_expr->range.start, ctx);
    return;
  }
  std::string name(prop.member->name);
  const void* built = nullptr;
  if (prop.kind == SyncKind::kSemaphore) {
    int32_t keys = SemaphoreKeyArg(new_expr, ctx, arena, 0);
    SemaphoreObject*& slot = (*SemaphoreMapOf(prop))[name];
    if (slot == nullptr) {
      slot = ctx.GetArena().Create<SemaphoreObject>(keys);
    } else {
      slot->key_count = keys;
    }
    built = slot;
  } else {
    int32_t bound = MailboxBoundArg(new_expr, ctx, arena);
    MailboxObject*& slot = (*MailboxMapOf(prop))[name];
    if (slot == nullptr) {
      slot = ctx.GetArena().Create<MailboxObject>(bound);
    } else {
      slot->Build(bound);
    }
    built = slot;
  }
  MirrorSyncCarrier(prop, SyncObjectIdentity(built), ctx);
}

static SyncHandle HandleOfProperty(const SyncProperty& prop) {
  if (prop.kind == SyncKind::kSemaphore) {
    return {prop.kind, HeldSyncObject(SemaphoreMapOf(prop), prop), nullptr};
  }
  return {prop.kind, nullptr, HeldSyncObject(MailboxMapOf(prop), prop)};
}

static SyncHandle HandleOfVariable(const Variable* var, const SimContext& ctx) {
  if (SemaphoreObject* sem = ctx.SemaphoreOfHandle(var))
    return {SyncKind::kSemaphore, sem, nullptr};
  if (MailboxObject* mbx = ctx.MailboxOfHandle(var))
    return {SyncKind::kMailbox, nullptr, mbx};
  return {};
}

static SyncHandle ResolveSyncHandle(const Expr* expr, SimContext& ctx,
                                    Arena& arena) {
  SyncProperty prop = ResolveSyncProperty(expr, ctx, arena);
  if (prop.kind != SyncKind::kNone) return HandleOfProperty(prop);
  if (expr->kind == ExprKind::kIdentifier) {
    if (const Variable* local = ctx.FindLocalVariable(expr->text))
      return HandleOfVariable(local, ctx);
  }
  std::string_view key = ScopedOrBareTargetKey(expr, arena);
  if (key.empty()) return {};
  if (SemaphoreObject* sem = ctx.FindSemaphore(key))
    return {SyncKind::kSemaphore, sem, nullptr};
  if (MailboxObject* mbx = ctx.FindMailbox(key))
    return {SyncKind::kMailbox, nullptr, mbx};
  return {};
}

static uint64_t IdentityOfHandle(const SyncHandle& handle) {
  if (handle.sem != nullptr) return SyncObjectIdentity(handle.sem);
  return SyncObjectIdentity(handle.mbx);
}

static void MarkShared(const SyncHandle& source) {
  if (source.sem != nullptr) source.sem->shared = true;
  if (source.mbx != nullptr) source.mbx->shared = true;
}

static void StoreSyncHandle(const SyncProperty& target,
                            const SyncHandle& source, SimContext& ctx) {
  std::string name(target.member->name);
  if (target.kind == SyncKind::kSemaphore) {
    (*SemaphoreMapOf(target))[name] = source.sem;
  } else {
    (*MailboxMapOf(target))[name] = source.mbx;
  }
  MirrorSyncCarrier(target, IdentityOfHandle(source), ctx);
  MarkShared(source);
}

static void InitSyncProperty(const SyncProperty& prop, const Expr* init,
                             SimContext& ctx) {
  if (init == nullptr) {
    MirrorSyncCarrier(prop, kNullClassHandle, ctx);
    return;
  }
  if (IsNewCall(init)) {
    BuildSyncProperty(prop, init, ctx, ctx.GetArena());
    return;
  }
  SyncHandle source = ResolveSyncHandle(init, ctx, ctx.GetArena());
  StoreSyncHandle(prop, source.kind == prop.kind ? source : SyncHandle{}, ctx);
}

bool TryInitClassSyncProperty(ClassObject* obj, const ClassTypeInfo* info,
                              std::string_view name, const Expr* init,
                              SimContext& ctx) {
  SyncMember member = SyncPropertyMember(info, name, ctx);
  if (member.member == nullptr || member.member->is_static) return false;
  InitSyncProperty(MakeSyncProperty(member, obj, std::string(name), ctx), init,
                   ctx);
  return true;
}

bool TryInitStaticSyncProperty(const ClassTypeInfo* info, std::string_view name,
                               const Expr* init, SimContext& ctx) {
  SyncMember member = SyncPropertyMember(info, name, ctx);
  if (member.member == nullptr || !member.member->is_static ||
      member.declaring != info) {
    return false;
  }
  InitSyncProperty(MakeSyncProperty(member, nullptr, std::string(name), ctx),
                   init, ctx);
  return true;
}

static void RebindScopedSyncHandle(const Stmt* stmt, bool is_null,
                                   SimContext& ctx, Arena& arena) {
  std::string_view key = ScopedOrBareTargetKey(stmt->lhs, arena);
  if (key.empty()) return;
  SemaphoreObject** sem_slot = ctx.SemaphoreSlot(key);
  MailboxObject** mbx_slot =
      sem_slot == nullptr ? ctx.MailboxSlot(key) : nullptr;
  if (sem_slot == nullptr && mbx_slot == nullptr) return;
  SyncHandle source =
      is_null ? SyncHandle{} : ResolveSyncHandle(stmt->rhs, ctx, arena);
  if (sem_slot != nullptr && (is_null || source.kind == SyncKind::kSemaphore)) {
    *sem_slot = source.sem;
  } else if (mbx_slot != nullptr &&
             (is_null || source.kind == SyncKind::kMailbox)) {
    *mbx_slot = source.mbx;
  } else {
    return;
  }
  MarkShared(source);
}

bool TrySyncHandleAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->rhs == nullptr) return false;
  SyncProperty target = ResolveSyncProperty(stmt->lhs, ctx, arena);
  bool is_null =
      stmt->rhs->kind == ExprKind::kIdentifier && stmt->rhs->text == "null";
  if (target.kind == SyncKind::kNone) {
    if (stmt->rhs->kind == ExprKind::kIdentifier ||
        stmt->rhs->kind == ExprKind::kMemberAccess) {
      RebindScopedSyncHandle(stmt, is_null, ctx, arena);
    }
    return false;
  }
  if (!HasStorage(target)) return false;
  SyncHandle source =
      is_null ? SyncHandle{} : ResolveSyncHandle(stmt->rhs, ctx, arena);
  if (!is_null && source.kind != target.kind) return false;
  StoreSyncHandle(target, source, ctx);
  return true;
}

SyncHandle ResolveSyncActual(SyncKind kind, const Expr* actual, SimContext& ctx,
                             Arena& arena) {
  SyncHandle handle;
  handle.kind = kind;
  if (kind == SyncKind::kNone || actual == nullptr) return handle;
  SyncHandle source = ResolveSyncHandle(actual, ctx, arena);
  if (source.kind == kind) return source;
  return handle;
}

void BindSyncFormal(const SyncHandle& actual, Variable* var, SimContext& ctx) {
  if (actual.kind == SyncKind::kSemaphore) {
    ctx.BindSemaphoreHandle(var, actual.sem);
  } else if (actual.kind == SyncKind::kMailbox) {
    ctx.BindMailboxHandle(var, actual.mbx);
  }
}

static const Variable* FormalOfReceiver(const Expr* recv, SimContext& ctx) {
  if (recv == nullptr || recv->kind != ExprKind::kIdentifier) return nullptr;
  return ctx.FindLocalVariable(recv->text);
}

SemaphoreObject* SemaphoreOfFormal(const Expr* recv, SimContext& ctx) {
  const Variable* var = FormalOfReceiver(recv, ctx);
  return var == nullptr ? nullptr : ctx.SemaphoreOfHandle(var);
}

MailboxObject* MailboxOfFormal(const Expr* recv, SimContext& ctx) {
  const Variable* var = FormalOfReceiver(recv, ctx);
  return var == nullptr ? nullptr : ctx.MailboxOfHandle(var);
}

static constexpr std::string_view kBuiltinBaseKey = "$base";

void BuildBuiltinSyncBase(ClassObject* obj, std::string_view base_class,
                          const Expr* super_new, SimContext& ctx,
                          Arena& arena) {
  if (obj == nullptr) return;
  std::string key(kBuiltinBaseKey);
  if (base_class == "semaphore") {
    obj->semaphore_properties[key] = ctx.GetArena().Create<SemaphoreObject>(
        super_new != nullptr ? SemaphoreKeyArg(super_new, ctx, arena, 0) : 0);
  } else if (base_class == "mailbox") {
    auto* mbx = ctx.GetArena().Create<MailboxObject>();
    mbx->Build(super_new != nullptr ? MailboxBoundArg(super_new, ctx, arena)
                                    : 0);
    obj->mailbox_properties[key] = mbx;
  }
}

static ClassObject* BuiltinBaseReceiver(const Expr* expr,
                                        std::string_view method,
                                        SimContext& ctx, Arena& arena) {
  if (expr == nullptr) return nullptr;
  if (expr->kind == ExprKind::kCall && expr->lhs != nullptr &&
      expr->lhs->kind == ExprKind::kIdentifier) {
    return expr->lhs->text == method ? ctx.CurrentThis() : nullptr;
  }
  const Expr* access = expr->kind == ExprKind::kCall ? expr->lhs : expr;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution || access->rhs == nullptr ||
      access->rhs->text != method) {
    return nullptr;
  }
  return HandleSideObject(access->lhs, ctx, arena);
}

SemaphoreObject* BuiltinBaseSemaphore(const Expr* expr, std::string_view method,
                                      SimContext& ctx, Arena& arena) {
  ClassObject* obj = BuiltinBaseReceiver(expr, method, ctx, arena);
  if (obj == nullptr) return nullptr;
  auto it = obj->semaphore_properties.find(std::string(kBuiltinBaseKey));
  return it == obj->semaphore_properties.end() ? nullptr : it->second;
}

MailboxObject* BuiltinBaseMailbox(const Expr* expr, std::string_view method,
                                  SimContext& ctx, Arena& arena) {
  ClassObject* obj = BuiltinBaseReceiver(expr, method, ctx, arena);
  if (obj == nullptr) return nullptr;
  auto it = obj->mailbox_properties.find(std::string(kBuiltinBaseKey));
  return it == obj->mailbox_properties.end() ? nullptr : it->second;
}

Logic4Vec NewContainedSyncObject(const Expr* new_expr,
                                 std::string_view class_type, SimContext& ctx,
                                 Arena& arena) {
  const void* obj = nullptr;
  if (BuiltinSyncKindOf(class_type, ctx) == SyncKind::kSemaphore) {
    auto* sem = ctx.GetArena().Create<SemaphoreObject>(
        SemaphoreKeyArg(new_expr, ctx, arena, 0));
    ctx.RecordContainedSemaphore(sem);
    obj = sem;
  } else {
    auto* mbx = ctx.GetArena().Create<MailboxObject>();
    mbx->Build(MailboxBoundArg(new_expr, ctx, arena));
    ctx.RecordContainedMailbox(mbx);
    obj = mbx;
  }
  return MakeLogic4VecVal(arena, 64, SyncObjectIdentity(obj));
}

void RecordContainedSyncHandle(const Expr* item, SimContext& ctx,
                               Arena& arena) {
  SyncHandle handle = ResolveSyncHandle(item, ctx, arena);
  if (handle.kind == SyncKind::kSemaphore) {
    ctx.RecordContainedSemaphore(handle.sem);
  } else if (handle.kind == SyncKind::kMailbox) {
    ctx.RecordContainedMailbox(handle.mbx);
  }
  MarkShared(handle);
}

SemaphoreObject* ContainedSemaphoreOf(const Expr* elem, SimContext& ctx,
                                      Arena& arena) {
  if (elem == nullptr || elem->kind != ExprKind::kSelect) return nullptr;
  return ctx.ContainedSemaphore(EvalExpr(elem, ctx, arena).ToUint64());
}

MailboxObject* ContainedMailboxOf(const Expr* elem, SimContext& ctx,
                                  Arena& arena) {
  if (elem == nullptr || elem->kind != ExprKind::kSelect) return nullptr;
  return ctx.ContainedMailbox(EvalExpr(elem, ctx, arena).ToUint64());
}

}  // namespace delta
