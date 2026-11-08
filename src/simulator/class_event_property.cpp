#include "simulator/class_event_property.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>

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

Variable* EventIn(Variable*& slot, Arena& arena) {
  if (slot == nullptr) {
    slot = arena.Create<Variable>();
    slot->value = MakeLogic4VecVal(arena, 1, 0);
    slot->is_event = true;
  }
  return slot;
}

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

Variable* OnClass(const ClassTypeInfo* cls, std::string_view name,
                  Arena& arena) {
  const ClassTypeInfo* declaring = nullptr;
  const ClassMember* member = EventPropertyDecl(cls, name, declaring);
  if (member == nullptr || !member->is_static) return nullptr;
  return EventIn(declaring->static_event_properties[std::string(name)], arena);
}

Variable* OfBareName(std::string_view name, SimContext& ctx, Arena& arena) {
  if (ClassObject* self = ctx.CurrentThis()) {
    if (Variable* ev = OnObject(self, name, arena)) return ev;
  }
  const ClassTypeInfo* cls = ctx.CurrentMethodClass();
  return cls != nullptr ? OnClass(cls, name, arena) : nullptr;
}

ClassObject* ObjectOfSide(const Expr* side, SimContext& ctx, Arena& arena) {
  if (ClassObject* obj = HandleSideObject(side, ctx, arena)) return obj;
  if (side->kind != ExprKind::kSelect) return nullptr;
  return ctx.GetClassObject(EvalExpr(side, ctx, arena).ToUint64());
}

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

static std::string EventIndexText(const Logic4Vec& index) {
  return index.is_string ? "\"" + Logic4VecToString(index) + "\""
                         : std::to_string(index.ToUint64());
}

static bool EventElementKey(const Expr* expr, SimContext& ctx, Arena& arena,
                            std::string& key, const Expr*& root) {
  if (expr == nullptr) return false;
  if (expr->kind == ExprKind::kIdentifier) {
    key = std::string(expr->text);
    root = expr;
    return true;
  }
  if (expr->kind != ExprKind::kSelect || expr->index_end != nullptr ||
      expr->index == nullptr ||
      !EventElementKey(expr->base, ctx, arena, key, root)) {
    return false;
  }
  key += "[" + EventIndexText(EvalExpr(expr->index, ctx, arena)) + "]";
  return true;
}

static Variable* QueueEventElement(const QueueObject& q, const Expr* select,
                                   SimContext& ctx, Arena& arena) {
  Logic4Vec index = EvalExpr(select->index, ctx, arena);
  uint64_t i = index.ToUint64();
  if (!q.holds_events || !index.IsKnown() || i >= q.elements.size()) {
    return nullptr;
  }
  return ctx.EventOfIdentity(q.elements[i].ToUint64());
}

static Variable* NewAssocEventElement(std::string key, SimContext& ctx,
                                      Arena& arena) {
  auto* stored =
      arena.Create<std::string>(ctx.ActiveInstancePrefix() + std::move(key));
  Variable* elem = ctx.CreateVariable(*stored, 1);
  elem->is_event = true;
  return elem;
}

Variable* EventArrayElement(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr == nullptr || expr->kind != ExprKind::kSelect) return nullptr;
  std::string key;
  const Expr* root = nullptr;
  if (!EventElementKey(expr, ctx, arena, key, root)) return nullptr;
  Variable* base = ctx.FindVariable(root->text);
  if (base == nullptr || !base->is_event) return nullptr;
  bool one_index = expr->base == root;
  if (const QueueObject* q = ctx.FindQueue(root->text)) {
    return one_index ? QueueEventElement(*q, expr, ctx, arena) : nullptr;
  }
  if (Variable* elem = ctx.FindVariable(key)) {
    return elem->is_event ? elem : nullptr;
  }
  if (!one_index || ctx.FindAssocArray(root->text) == nullptr) return nullptr;
  return NewAssocEventElement(std::move(key), ctx, arena);
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
