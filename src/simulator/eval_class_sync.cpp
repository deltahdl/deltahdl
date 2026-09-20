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
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_mailbox.h"
#include "simulator/eval_semaphore.h"
#include "simulator/sim_context.h"
#include "simulator/sync_objects.h"

namespace delta {

// §6.18 (printed page 118 of ~/LRM.pdf): a typedef name stands for the type
// it was declared with, which may be another typedef name, and §26.3 reaches
// a package's under `p::name`, the key the run records it by. The written
// name is followed through the chain to the name at its end, at most as many
// steps as the table has entries, so a chain that returns to itself ends.
SyncKind SyncKindOfType(const DataType& type, const SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed) return SyncKind::kNone;
  std::string name =
      type.scope_name.empty()
          ? std::string(type.type_name)
          : std::string(type.scope_name) + "::" + std::string(type.type_name);
  for (size_t steps = 0; steps <= ctx.TypeTargetCount(); ++steps) {
    if (name == "semaphore") return SyncKind::kSemaphore;
    if (name == "mailbox") return SyncKind::kMailbox;
    std::string_view target = ctx.FindTypeTarget(name);
    if (target.empty()) return SyncKind::kNone;
    name = std::string(target);
  }
  return SyncKind::kNone;
}

// A property's declaration and the class that declares it, whose maps hold
// the object where the property is static (§8.9).
struct SyncMember {
  const ClassMember* member = nullptr;
  const ClassTypeInfo* declaring = nullptr;
};

// §8.13: the declaration of the property `name` nearest to `from` on its
// base chain, the one a bare name in a method of `from` denotes, of
// whatever type, with the class declaring it; none where no class of the
// chain declares the name.
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

static bool IsSyncMember(const SyncMember& m, const SimContext& ctx) {
  return m.member != nullptr && !m.member->is_param &&
         m.member->unpacked_dims.empty() &&
         SyncKindOfType(m.member->data_type, ctx) != SyncKind::kNone;
}

// The nearest declaration of `name` on the base chain of `from`, where it
// is a property of a semaphore or mailbox type with no unpacked dimension,
// static (§8.9) or not; none where the nearest declaration is anything else
// or none declares the name.
static SyncMember SyncPropertyMember(const ClassTypeInfo* from,
                                     std::string_view name,
                                     const SimContext& ctx) {
  SyncMember nearest = NearestPropertyDecl(from, name);
  return IsSyncMember(nearest, ctx) ? nearest : SyncMember{};
}

// §8.23 (printed pages 200-201): a nested class's method reaches the static
// properties of the classes enclosing it, innermost first, by their bare
// names, and a non-static one only through a handle. The nearest
// declaration of `name` on the base chain of the class nearest to `from`
// that declares one, where it is a static semaphore or mailbox property;
// none where that declaration is anything else, or no enclosing class
// declares the name. Asked of a bare name only once the base chain of
// `from` itself declares nothing of the name (§8.13), as StaticPropertyOwner
// walks the chain for a static value property. Walked along the base chain
// alone, `mb.put(v)` in the nested class reached nothing.
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
  return {SyncKindOfType(m.member->data_type, ctx), obj, m.member, m.declaring,
          std::move(spelling)};
}

// The receiver as it was written, `c.mb` or `C::mb`, for a report to name.
static std::string SpellHandlePath(const Expr* expr) {
  if (expr->kind == ExprKind::kIdentifier) return std::string(expr->text);
  return SpellHandlePath(expr->lhs) + (expr->is_scope_resolution ? "::" : ".") +
         std::string(expr->rhs->text);
}

// §8.11 with §8.13: the bare name `name` inside a method, resolved against
// the lexically enclosing class or, in a property initializer or a
// constructor with no class pushed, the running object's own. A local of
// the method -- a formal named as the property is -- shadows the property
// (§8.6), as it shadows a queue property in FindQueueOfName. A static
// method has no object (§8.10) and reaches a static property all the same.
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

// §8.4: the class the handle side `side` of a member access is declared of,
// for naming the property a null handle would have reached: the class a
// variable was declared with, or the one a property of the running object
// names (§8.25's type parameter read through the object), or the enclosing
// class for a `this` no object stands behind (a static method, §8.10).
// Null for a longer path, whose declared class is not followed.
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

// §8.4: `h.name` or `this.name`, the property of the object the handle side
// refers to, or, where it refers to none, the property the handle's declared
// class gives that name, so that the null handle is reported rather than the
// receiver resolved through the run's tables to a variable of the name; a
// static one (§8.9) is the class's and is served through a null handle too.
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

// §8.9 (printed page 186) with §8.23: `C::name`, the static property `name`
// of the class C, which needs no object. A package's `p::name` names no
// class and is left to the run's tables.
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

// §8.4: the report for a method reached through a property that holds no
// semaphore or mailbox, or through a null handle, worded as
// ResolveThroughNullHandle words it for a method of a user class.
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

// §8.9 with §8.4: the map the property's object stands in -- the declaring
// class's for a static property, the object's otherwise -- or null for an
// instance property with no object, whose access is illegal.
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

// The semaphore or mailbox the property holds, or null where it holds none.
// §8.9: a static property is created once, at the class's static
// initialization (TryInitStaticSyncProperty), which leaves the map an entry
// for it -- an entry, null included, is what that or an assignment left.
// A static property whose map has no entry is one the pass did not know
// for a semaphore or mailbox, and its one copy is built here on the first
// reference from the declaration's `new`: PopulateClassType
// (lowerer_class.cpp) runs the pass for every class, top-level and nested,
// but a unit's or a package's class is lowered before RegisterClassTypeAliases
// fills the typedef table, so a static property declared through a typedef
// (§15.4.9's `s_mbox`) is built here, reading its argument at that first
// reference.
template <typename T>
static T* HeldSyncObject(std::unordered_map<std::string, T*>* held,
                         const SyncProperty& prop, SimContext& ctx) {
  if (held == nullptr) return nullptr;
  std::string name(prop.member->name);
  auto it = held->find(name);
  if (it != held->end()) return it->second;
  if (!prop.member->is_static || !IsNewCall(prop.member->init_expr))
    return nullptr;
  BuildSyncProperty(prop, prop.member->init_expr, ctx, ctx.GetArena());
  return (*held)[name];
}

SemaphoreObject* SemaphoreOfProperty(const SyncProperty& prop,
                                     std::string_view method, SourceLoc loc,
                                     SimContext& ctx) {
  if (prop.kind != SyncKind::kSemaphore) return nullptr;
  SemaphoreObject* sem = HeldSyncObject(SemaphoreMapOf(prop), prop, ctx);
  if (sem == nullptr) ReportNullSyncProperty(prop, method, loc, ctx);
  return sem;
}

MailboxObject* MailboxOfProperty(const SyncProperty& prop,
                                 std::string_view method, SourceLoc loc,
                                 SimContext& ctx) {
  if (prop.kind != SyncKind::kMailbox) return nullptr;
  MailboxObject* mbx = HeldSyncObject(MailboxMapOf(prop), prop, ctx);
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
  if (prop.kind == SyncKind::kSemaphore) {
    int32_t keys = SemaphoreKeyArg(new_expr, ctx, arena, 0);
    SemaphoreObject*& slot = (*SemaphoreMapOf(prop))[name];
    if (slot == nullptr) {
      slot = ctx.GetArena().Create<SemaphoreObject>(keys);
    } else {
      slot->key_count = keys;
    }
    return;
  }
  int32_t bound = MailboxBoundArg(new_expr, ctx, arena);
  MailboxObject*& slot = (*MailboxMapOf(prop))[name];
  if (slot == nullptr) {
    slot = ctx.GetArena().Create<MailboxObject>(bound);
  } else {
    slot->Build(bound);
  }
}

static SyncHandle HandleOfProperty(const SyncProperty& prop, SimContext& ctx) {
  if (prop.kind == SyncKind::kSemaphore) {
    return {prop.kind, HeldSyncObject(SemaphoreMapOf(prop), prop, ctx),
            nullptr};
  }
  return {prop.kind, nullptr, HeldSyncObject(MailboxMapOf(prop), prop, ctx)};
}

static SyncHandle HandleOfVariable(const Variable* var, const SimContext& ctx) {
  if (SemaphoreObject* sem = ctx.SemaphoreOfHandle(var))
    return {SyncKind::kSemaphore, sem, nullptr};
  if (MailboxObject* mbx = ctx.MailboxOfHandle(var))
    return {SyncKind::kMailbox, nullptr, mbx};
  return {};
}

// §15.3 and §15.4 with §8.12: the semaphore or mailbox `expr` is a handle
// to -- a property's (HandleOfProperty), a formal's (§13.5.1, a local of the
// name shadowing the run's tables), or a module's, an instance's or a
// package's by name or by `p::name` (ScopedOrBareTargetKey).
static SyncHandle ResolveSyncHandle(const Expr* expr, SimContext& ctx,
                                    Arena& arena) {
  SyncProperty prop = ResolveSyncProperty(expr, ctx, arena);
  if (prop.kind != SyncKind::kNone) return HandleOfProperty(prop, ctx);
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

// §8.12: the property `target` made a handle to the object `source` names,
// the same object under two names.
static void StoreSyncHandle(const SyncProperty& target,
                            const SyncHandle& source) {
  std::string name(target.member->name);
  if (target.kind == SyncKind::kSemaphore) {
    (*SemaphoreMapOf(target))[name] = source.sem;
  } else {
    (*MailboxMapOf(target))[name] = source.mbx;
  }
}

// §8.7 and §8.9: the property's initializer `init` -- a `new(...)`, which
// builds the object in the property's map, or any other expression, which
// makes the property a handle to the semaphore or mailbox it names (§8.12)
// or leaves it null where it names none.
static void InitSyncProperty(const SyncProperty& prop, const Expr* init,
                             SimContext& ctx) {
  if (IsNewCall(init)) {
    BuildSyncProperty(prop, init, ctx, ctx.GetArena());
    return;
  }
  SyncHandle source = ResolveSyncHandle(init, ctx, ctx.GetArena());
  StoreSyncHandle(prop, source.kind == prop.kind ? source : SyncHandle{});
}

bool TryInitClassSyncProperty(ClassObject* obj, const ClassTypeInfo* info,
                              std::string_view name, const Expr* init,
                              SimContext& ctx) {
  SyncMember member = SyncPropertyMember(info, name, ctx);
  if (member.member == nullptr || member.member->is_static) return false;
  if (init == nullptr) return true;
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
  if (init == nullptr) return true;
  InitSyncProperty(MakeSyncProperty(member, nullptr, std::string(name), ctx),
                   init, ctx);
  return true;
}

bool TrySyncHandleAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->rhs == nullptr) return false;
  SyncProperty target = ResolveSyncProperty(stmt->lhs, ctx, arena);
  if (target.kind == SyncKind::kNone || !HasStorage(target)) return false;
  bool is_null =
      stmt->rhs->kind == ExprKind::kIdentifier && stmt->rhs->text == "null";
  SyncHandle source =
      is_null ? SyncHandle{} : ResolveSyncHandle(stmt->rhs, ctx, arena);
  if (!is_null && source.kind != target.kind) return false;
  StoreSyncHandle(target, source);
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

}  // namespace delta
