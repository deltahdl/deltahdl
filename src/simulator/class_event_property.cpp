#include "simulator/class_event_property.h"

#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// The declaration of the property `name` on the class chain from `type` where
// it is an event, `event e` or `static event e`, with the class declaring it
// in `declaring`. The nearest declaration of the name answers (§8.13), so a
// class between that redeclares it as anything else hides the event and
// answers null.
const ClassMember* EventPropertyDecl(const ClassTypeInfo* type,
                                     std::string_view name,
                                     const ClassTypeInfo*& declaring) {
  for (const ClassTypeInfo* t = type; t != nullptr; t = t->parent) {
    if (t->decl == nullptr) continue;
    for (const ClassMember* member : t->decl->members) {
      if (member->kind != ClassMemberKind::kProperty || member->name != name)
        continue;
      if (member->data_type.kind != DataTypeKind::kEvent ||
          !member->unpacked_dims.empty()) {
        return nullptr;
      }
      declaring = t;
      return member;
    }
  }
  return nullptr;
}

// The event in `slot`, made on the first reference: a variable of the event
// kind, one bit wide, that no trigger has set.
Variable* EventIn(Variable*& slot, Arena& arena) {
  if (slot == nullptr) {
    slot = arena.Create<Variable>();
    slot->value = MakeLogic4VecVal(arena, 1, 0);
    slot->is_event = true;
  }
  return slot;
}

// The event the property `name` holds on the object `obj`, the class's own
// where the property is static (§8.9).
Variable* OnObject(ClassObject* obj, std::string_view name, Arena& arena) {
  const ClassTypeInfo* declaring = nullptr;
  const ClassMember* member = EventPropertyDecl(obj->type, name, declaring);
  if (member == nullptr) return nullptr;
  if (member->is_static) {
    return EventIn(declaring->static_event_properties[std::string(name)],
                   arena);
  }
  return EventIn(obj->event_properties[std::string(name)], arena);
}

// The event the static property `name` of the class chain from `cls` holds.
Variable* OnClass(const ClassTypeInfo* cls, std::string_view name,
                  Arena& arena) {
  const ClassTypeInfo* declaring = nullptr;
  const ClassMember* member = EventPropertyDecl(cls, name, declaring);
  if (member == nullptr || !member->is_static) return nullptr;
  return EventIn(declaring->static_event_properties[std::string(name)], arena);
}

// A bare name inside a method: the running object's event property, else the
// running class's static one.
Variable* OfBareName(std::string_view name, SimContext& ctx, Arena& arena) {
  if (ClassObject* self = ctx.CurrentThis()) {
    if (Variable* ev = OnObject(self, name, arena)) return ev;
  }
  const ClassTypeInfo* cls = ctx.CurrentMethodClass();
  return cls != nullptr ? OnClass(cls, name, arena) : nullptr;
}

// The object the left side of `side.ev` designates: a handle path names its
// object without evaluating anything (HandleSideObject), and an element of an
// array of handles, `m_events[obj]`, is read for the handle it holds.
ClassObject* ObjectOfSide(const Expr* side, SimContext& ctx, Arena& arena) {
  if (ClassObject* obj = HandleSideObject(side, ctx, arena)) return obj;
  if (side->kind != ExprKind::kSelect) return nullptr;
  return ctx.GetClassObject(EvalExpr(side, ctx, arena).ToUint64());
}

// `C::ev`, a static event property named through its class.
Variable* OfScopeForm(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->lhs->kind != ExprKind::kIdentifier) return nullptr;
  const ClassTypeInfo* cls = ctx.FindClassType(expr->lhs->text);
  return cls != nullptr ? OnClass(cls, expr->rhs->text, arena) : nullptr;
}

}  // namespace

Variable* ClassEventVariable(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr == nullptr) return nullptr;
  if (expr->kind == ExprKind::kIdentifier)
    return OfBareName(expr->text, ctx, arena);
  if (expr->kind != ExprKind::kMemberAccess || expr->lhs == nullptr ||
      expr->rhs == nullptr || expr->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  if (expr->is_scope_resolution) return OfScopeForm(expr, ctx, arena);
  ClassObject* obj = ObjectOfSide(expr->lhs, ctx, arena);
  return obj != nullptr ? OnObject(obj, expr->rhs->text, arena) : nullptr;
}

Variable* EventArrayElement(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr == nullptr || expr->kind != ExprKind::kSelect ||
      expr->index_end != nullptr || expr->index == nullptr ||
      expr->base == nullptr || expr->base->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  Variable* base = ctx.FindVariable(expr->base->text);
  if (base == nullptr || !base->is_event) return nullptr;
  Logic4Vec index = EvalExpr(expr->index, ctx, arena);
  if (const QueueObject* q = ctx.FindQueue(expr->base->text)) {
    uint64_t i = index.ToUint64();
    if (!q->holds_events || !index.IsKnown() || i >= q->elements.size()) {
      return nullptr;
    }
    return ctx.EventOfIdentity(q->elements[i].ToUint64());
  }
  std::string key = std::string(expr->base->text) + "[" +
                    (index.is_string ? "\"" + Logic4VecToString(index) + "\""
                                     : std::to_string(index.ToUint64())) +
                    "]";
  if (Variable* elem = ctx.FindVariable(key)) {
    return elem->is_event ? elem : nullptr;
  }
  if (ctx.FindAssocArray(expr->base->text) == nullptr) return nullptr;
  auto* stored =
      arena.Create<std::string>(ctx.ActiveInstancePrefix() + std::move(key));
  Variable* elem = ctx.CreateVariable(*stored, 1);
  elem->is_event = true;
  return elem;
}

Logic4Vec EventIdentityOf(const Expr* expr, SimContext& ctx, Arena& arena) {
  std::string_view name =
      expr != nullptr && expr->kind == ExprKind::kIdentifier ? expr->text : "";
  Variable* event = TriggerTargetEvent(expr, name, ctx);
  uint64_t identity = event != nullptr && event->is_event
                          ? ctx.RegisterEventIdentity(event)
                          : 0;
  return MakeLogic4VecVal(arena, 64, identity);
}

Variable* TriggerTargetEvent(const Expr* expr, std::string_view name,
                             SimContext& ctx) {
  if (!name.empty()) {
    if (Variable* var = ctx.FindVariable(name)) return var;
  }
  if (Variable* var = ClassEventVariable(expr, ctx, ctx.GetArena())) {
    return var;
  }
  return EventArrayElement(expr, ctx, ctx.GetArena());
}

bool TryClassEventTriggered(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out) {
  if (expr == nullptr) return false;
  const Expr* access = expr->kind == ExprKind::kCall ? expr->lhs : expr;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution || access->rhs == nullptr ||
      access->rhs->text != "triggered") {
    return false;
  }
  Variable* event = ClassEventVariable(access->lhs, ctx, arena);
  if (event == nullptr) return false;
  bool now = !event->is_null_event &&
             event->triggered_ticks == ctx.CurrentTime().ticks;
  out = MakeLogic4VecVal(arena, 1, now ? 1u : 0u);
  return true;
}

}  // namespace delta
