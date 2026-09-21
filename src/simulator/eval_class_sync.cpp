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
#include "simulator/sim_context.h"
#include "simulator/sync_objects.h"

namespace delta {

// §26.2 (printed page 808 of IEEE 1800-2023): a package's declarations
// are visible by their bare names throughout the package, its classes included,
// and the run keys a package's typedef "pkg::name" (RegisterTypeDeclarations
// in lowerer_register.cpp), the bare key standing only where a module's
// import added it. So a name written bare in a class the package `package`
// declares -- the property's own type, or a step of its chain, which the
// targets record bare -- is looked up under the package's key first and
// then under its own; a name written with a scope, `q::t`, under that
// alone. Empty where nothing records the name. Looked up bare alone, the
// `mb_t mb = new` of p's own class found nothing while no module imported p
// and the property was no mailbox.
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

// §6.18 (printed page 118 of IEEE 1800-2023): a typedef name stands for
// the type it was declared with, which may be another typedef name, and §26.3
// reaches a package's under `p::name`, the key the run records it by. The
// written name is followed through the chain to the name at its end, at most as
// many steps as the table has entries, so a chain that returns to itself ends.
SyncKind SyncKindOfType(const DataType& type, std::string_view package,
                        const SimContext& ctx) {
  if (type.kind != DataTypeKind::kNamed) return SyncKind::kNone;
  std::string name =
      type.scope_name.empty()
          ? std::string(type.type_name)
          : std::string(type.scope_name) + "::" + std::string(type.type_name);
  for (size_t steps = 0; steps <= ctx.TypeTargetCount(); ++steps) {
    if (name == "semaphore") return SyncKind::kSemaphore;
    if (name == "mailbox") return SyncKind::kMailbox;
    std::string_view target = TypeTargetFor(name, package, ctx);
    if (target.empty()) return SyncKind::kNone;
    name = std::string(target);
  }
  return SyncKind::kNone;
}

SyncKind SyncKindOfType(const DataType& type, const SimContext& ctx) {
  return SyncKindOfType(type, {}, ctx);
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

// The kind of the property `m` declares, its type read in the package the
// declaring class stands in (ClassTypeInfo::package, §26.2).
static SyncKind SyncKindOfMember(const SyncMember& m, const SimContext& ctx) {
  return SyncKindOfType(m.member->data_type, m.declaring->package, ctx);
}

static bool IsSyncMember(const SyncMember& m, const SimContext& ctx) {
  return m.member != nullptr && !m.member->is_param &&
         m.member->unpacked_dims.empty() &&
         SyncKindOfMember(m, ctx) != SyncKind::kNone;
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
  return {SyncKindOfMember(m, ctx), obj, m.member, m.declaring,
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

// §8.4 (printed pages 181-182 of IEEE 1800-2023): a handle is compared
// with null by whether it refers to an object, an uninitialized one holding
// null, and §15.3 (printed 372) and §15.4 (printed 374) make a semaphore or
// mailbox variable a handle to the bucket or the queue. The value under the
// property's name is what `mb == null`, `if (mb)` and `c.mb != null` read
// through the generic paths, so it is kept beside the map as the handle's
// carrier: the identity of the object the map holds (SyncObjectIdentity in
// sync_objects.h), so that `c.x == c.y` reads whether the two refer to one
// object, and kNullClassHandle while it holds none, as a class handle's is
// for null; a 1 for every object compared two properties each built by its
// own `new` equal. An instance property's is
// written under the declaring class's scoped key and, where no class
// between the object's own and the declaring one shadows the name (§8.15),
// the bare one, the pair ClassObject::SetPropertyForType writes; a static
// property's into the class's own storage (§8.9). Left at the 0 the
// construction stored, a property holding a mailbox compared equal to null.
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

// The semaphore or mailbox the property holds, or null where it holds none:
// the entry the construction (TryInitClassSyncProperty), the class's static
// initialization (§8.9, TryInitStaticSyncProperty) or an assignment left,
// null included, or no entry for an instance property with no object. A
// static property declared through a typedef was built here on the first
// reference, the typedef table being filled after the packages' and the
// unit's classes were lowered (RegisterClassTypeAliases); the table is
// filled ahead of every class now (RegisterTypeTargets in
// lowerer_register.cpp), so every static one is built at lowering.
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

// §15.3 and §15.4 with §8.12: the semaphore or mailbox `expr` is a handle
// to -- a property's (HandleOfProperty), a formal's (§13.5.1, a local of the
// name shadowing the run's tables), or a module's, an instance's or a
// package's by name or by `p::name` (ScopedOrBareTargetKey).
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

// The identity of the object a handle refers to, null where it holds none.
static uint64_t IdentityOfHandle(const SyncHandle& handle) {
  if (handle.sem != nullptr) return SyncObjectIdentity(handle.sem);
  return SyncObjectIdentity(handle.mbx);
}

// §8.12: the property `target` made a handle to the object `source` names,
// the same object under two names, or the null handle where `source` holds
// none, its carrier following (MirrorSyncCarrier).
static void StoreSyncHandle(const SyncProperty& target,
                            const SyncHandle& source, SimContext& ctx) {
  std::string name(target.member->name);
  if (target.kind == SyncKind::kSemaphore) {
    (*SemaphoreMapOf(target))[name] = source.sem;
  } else {
    (*MailboxMapOf(target))[name] = source.mbx;
  }
  MirrorSyncCarrier(target, IdentityOfHandle(source), ctx);
}

// §8.7 and §8.9: the property's initializer `init` -- a `new(...)`, which
// builds the object in the property's map, or any other expression, which
// makes the property a handle to the semaphore or mailbox it names (§8.12)
// or leaves it null where it names none; no initializer leaves it the null
// handle §8.4 (printed page 182) gives an uninitialized one, its carrier 0.
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

bool TrySyncHandleAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->rhs == nullptr) return false;
  SyncProperty target = ResolveSyncProperty(stmt->lhs, ctx, arena);
  if (target.kind == SyncKind::kNone || !HasStorage(target)) return false;
  bool is_null =
      stmt->rhs->kind == ExprKind::kIdentifier && stmt->rhs->text == "null";
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

}  // namespace delta
