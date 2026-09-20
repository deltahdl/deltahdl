#include "simulator/eval_class_sync.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_mailbox.h"
#include "simulator/eval_semaphore.h"
#include "simulator/sim_context.h"
#include "simulator/sync_objects.h"

namespace delta {

SyncKind SyncKindOfType(const DataType& type) {
  if (type.kind != DataTypeKind::kNamed) return SyncKind::kNone;
  if (type.type_name == "semaphore") return SyncKind::kSemaphore;
  if (type.type_name == "mailbox") return SyncKind::kMailbox;
  return SyncKind::kNone;
}

// §8.13: the declaration of the property `name` nearest to `from` on its
// base chain, the one a bare name in a method of `from` denotes, where that
// declaration is an instance property of a semaphore or mailbox type with
// no unpacked dimension; null where the nearest declaration is anything
// else or none declares the name. A static one (§8.9) is the class's rather
// than an object's and is left to the run's tables, which hold none today.
static const ClassMember* SyncPropertyMember(const ClassTypeInfo* from,
                                             std::string_view name) {
  for (const ClassTypeInfo* t = from; t != nullptr; t = t->parent) {
    if (t->decl == nullptr) continue;
    for (const ClassMember* m : t->decl->members) {
      if (m->kind != ClassMemberKind::kProperty || m->name != name) continue;
      bool held_per_object = !m->is_static && !m->is_param &&
                             m->unpacked_dims.empty() &&
                             SyncKindOfType(m->data_type) != SyncKind::kNone;
      return held_per_object ? m : nullptr;
    }
  }
  return nullptr;
}

// The receiver as it was written, `c.mb` for a report to name.
static std::string SpellHandlePath(const Expr* expr) {
  if (expr->kind == ExprKind::kIdentifier) return std::string(expr->text);
  return SpellHandlePath(expr->lhs) + "." + std::string(expr->rhs->text);
}

// §8.11 with §8.13: the bare name `name` inside a method, resolved against
// the lexically enclosing class or, in a property initializer or a
// constructor with no class pushed, the running object's own. A local of
// the method -- a formal named as the property is -- shadows the property
// (§8.6), as it shadows a queue property in FindQueueOfName.
static SyncProperty ResolveBareSyncProperty(std::string_view name,
                                            SimContext& ctx) {
  ClassObject* self = ctx.CurrentThis();
  const ClassTypeInfo* from = ctx.CurrentMethodClass();
  if (from == nullptr && self != nullptr) from = self->type;
  if (from == nullptr || ctx.FindLocalVariable(name) != nullptr) return {};
  const ClassMember* member = SyncPropertyMember(from, name);
  if (member == nullptr) return {};
  return {SyncKindOfType(member->data_type), self, member, std::string(name)};
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
// receiver resolved through the run's tables to a variable of the name.
static SyncProperty ResolveSyncPropertyThroughHandle(const Expr* recv,
                                                     SimContext& ctx,
                                                     Arena& arena) {
  std::string_view name = recv->rhs->text;
  if (ClassObject* obj = HandleSideObject(recv->lhs, ctx, arena)) {
    const ClassMember* member = SyncPropertyMember(obj->type, name);
    if (member == nullptr) return {};
    return {SyncKindOfType(member->data_type), obj, member,
            SpellHandlePath(recv)};
  }
  const ClassTypeInfo* cls = DeclaredClassOfHandleSide(recv->lhs, ctx);
  const ClassMember* member =
      cls != nullptr ? SyncPropertyMember(cls, name) : nullptr;
  if (member == nullptr) return {};
  return {SyncKindOfType(member->data_type), nullptr, member,
          SpellHandlePath(recv->lhs)};
}

SyncProperty ResolveSyncProperty(const Expr* recv, SimContext& ctx,
                                 Arena& arena) {
  if (recv == nullptr) return {};
  if (recv->kind == ExprKind::kIdentifier && recv->text != "this") {
    return ResolveBareSyncProperty(recv->text, ctx);
  }
  if (recv->kind != ExprKind::kMemberAccess || recv->is_scope_resolution ||
      recv->rhs == nullptr || recv->rhs->kind != ExprKind::kIdentifier ||
      !IsHandlePath(recv->lhs)) {
    return {};
  }
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

// The semaphore or mailbox the object holds under the property's name, or
// null where the entry is absent or null.
template <typename T>
static T* HeldSyncObject(const std::unordered_map<std::string, T*>& held,
                         std::string_view name) {
  auto it = held.find(std::string(name));
  return it == held.end() ? nullptr : it->second;
}

SemaphoreObject* SemaphoreOfProperty(const SyncProperty& prop,
                                     std::string_view method, SourceLoc loc,
                                     SimContext& ctx) {
  if (prop.kind != SyncKind::kSemaphore) return nullptr;
  SemaphoreObject* sem =
      prop.obj == nullptr
          ? nullptr
          : HeldSyncObject(prop.obj->semaphore_properties, prop.member->name);
  if (sem == nullptr) ReportNullSyncProperty(prop, method, loc, ctx);
  return sem;
}

MailboxObject* MailboxOfProperty(const SyncProperty& prop,
                                 std::string_view method, SourceLoc loc,
                                 SimContext& ctx) {
  if (prop.kind != SyncKind::kMailbox) return nullptr;
  MailboxObject* mbx =
      prop.obj == nullptr
          ? nullptr
          : HeldSyncObject(prop.obj->mailbox_properties, prop.member->name);
  if (mbx == nullptr) ReportNullSyncProperty(prop, method, loc, ctx);
  return mbx;
}

void BuildSyncProperty(const SyncProperty& prop, const Expr* new_expr,
                       SimContext& ctx, Arena& arena) {
  if (prop.obj == nullptr) {
    ReportNullSyncProperty(prop, "new", new_expr->range.start, ctx);
    return;
  }
  std::string name(prop.member->name);
  if (prop.kind == SyncKind::kSemaphore) {
    int32_t keys = SemaphoreKeyArg(new_expr, ctx, arena, 0);
    SemaphoreObject*& slot = prop.obj->semaphore_properties[name];
    if (slot == nullptr) {
      slot = ctx.GetArena().Create<SemaphoreObject>(keys);
    } else {
      slot->key_count = keys;
    }
    return;
  }
  int32_t bound = MailboxBoundArg(new_expr, ctx, arena);
  MailboxObject*& slot = prop.obj->mailbox_properties[name];
  if (slot == nullptr) {
    slot = ctx.GetArena().Create<MailboxObject>(bound);
  } else {
    slot->Build(bound);
  }
}

bool TryInitClassSyncProperty(ClassObject* obj, const ClassTypeInfo* info,
                              std::string_view name, const Expr* init,
                              SimContext& ctx) {
  const ClassMember* member = SyncPropertyMember(info, name);
  if (member == nullptr) return false;
  if (init == nullptr || init->kind != ExprKind::kCall || init->text != "new")
    return true;
  SyncProperty prop{SyncKindOfType(member->data_type), obj, member,
                    std::string(name)};
  BuildSyncProperty(prop, init, ctx, ctx.GetArena());
  return true;
}

}  // namespace delta
