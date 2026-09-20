#include "simulator/eval_array_class_queue.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/queue_dim.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/evaluation.h"
#include "simulator/queue_bound.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

namespace {

// §8.5/§7.10: whether the property declaration `member` is a queue: one
// unpacked dimension written `[$]` or `[$:N]` (Syntax 7-4).
bool DeclaresQueueProperty(const ClassMember* member) {
  return !member->is_param && member->unpacked_dims.size() == 1 &&
         IsQueueDim(member->unpacked_dims[0]);
}

// §8.5/§7.10: the declaration of the property `name` on the class chain from
// `type` whose one unpacked dimension is a queue dimension, and the class
// that declares it in `declaring`. The nearest declaration is the one that
// answers (§8.13): a class between that redeclares the name as something else
// hides the queue below it, and answers null.
const ClassMember* FindQueuePropertyDecl(const ClassTypeInfo* type,
                                         std::string_view name,
                                         const ClassTypeInfo*& declaring) {
  for (const auto* t = type; t != nullptr; t = t->parent) {
    if (t->decl == nullptr) continue;
    for (const auto* member : t->decl->members) {
      if (member->kind != ClassMemberKind::kProperty || member->name != name)
        continue;
      if (!DeclaresQueueProperty(member)) return nullptr;
      declaring = t;
      return member;
    }
  }
  return nullptr;
}

// The name a written type stands under: the name of a named type, or the
// identifier the parser records an actual or a default written as a bare name
// as (`#(my_t)` arrives as an implicit type carrying the name as an
// expression). Empty for a type with no name of its own.
std::string_view TypeNameOf(const DataType& type) {
  if (!type.type_name.empty()) return type.type_name;
  if (type.type_ref_expr != nullptr &&
      type.type_ref_expr->kind == ExprKind::kIdentifier) {
    return type.type_ref_expr->text;
  }
  return {};
}

// §8.4: whether the element type of the property `member` of `decl` on `obj`
// is a class, so that each element is a handle: the type the declaration
// names, or, where it names a type parameter (§8.25), the type the object's
// specialization binds that parameter to, else the default the class
// declares, as §8.26's `T myFifo[$:DEPTH-1]` on a `Fifo#(Item)`.
bool ElementTypeIsClass(const ClassMember* member, const ClassDecl* decl,
                        const ClassObject* obj, SimContext& ctx) {
  std::string_view name = TypeNameOf(member->data_type);
  if (name.empty()) return false;
  if (decl->type_param_names.count(name) != 0) {
    const DataType* bound = TypeParamActual(obj, decl, name);
    if (bound == nullptr) return false;
    name = TypeNameOf(*bound);
  }
  return !name.empty() && ctx.FindClassType(name) != nullptr;
}

// §7.10.5: the element count the dimension `dim` allows, N + 1 for `[$:N]`,
// and -1, which QueueObject spells unbounded, for `[$]` and for an N Syntax
// 7-4 rules out. §8.25: N may name a parameter of the class, `DEPTH-1` in
// §8.26's Fifo, whose value in this specialization the object holds as a
// property of its own (ApplyClassParamOverrides in eval_function.cpp), so the
// bound is evaluated with the object as `this` and no method class in force:
// a bare name then reads the object's value rather than the class's default.
int32_t PropertyQueueBound(const Expr* dim, ClassObject* obj, SimContext& ctx) {
  if (dim->rhs == nullptr) return -1;
  if (obj != nullptr) {
    ctx.PushThis(obj);
    ctx.PushMethodClass(nullptr);
  }
  Logic4Vec val = EvalExpr(dim->rhs, ctx, ctx.GetArena());
  if (obj != nullptr) {
    ctx.PopMethodClass();
    ctx.PopThis();
  }
  if (!val.IsKnown()) return -1;
  auto bound = static_cast<int64_t>(val.ToUint64());
  if (auto size = QueueBoundMaxSize(bound)) return *size;
  return -1;
}

// §7.10: the queue the declaration `member` of class `declaring` asks for on
// `obj`, empty. The element takes the width and state-ness the class's
// property record gives it, which is what a scalar property of the same
// declaration is written with; the bound is PropertyQueueBound's.
QueueObject* MakeQueueProperty(const ClassTypeInfo* declaring,
                               const ClassMember* member, ClassObject* obj,
                               SimContext& ctx) {
  const auto* prop = declaring->FindProperty(member->name);
  auto* q = ctx.GetArena().Create<QueueObject>();
  q->elem_width = prop != nullptr ? prop->width : 32;
  q->is_4state = prop != nullptr && prop->is_4state;
  q->max_size = PropertyQueueBound(member->unpacked_dims[0], obj, ctx);
  q->holds_class_handles =
      ElementTypeIsClass(member, declaring->decl, obj, ctx);
  return q;
}

// The queue ClassQueueProperty answers, with `owner` set to the object whose
// property it is, or to null for a static property's, which no object owns.
QueueObject* ResolveOn(ClassObject* obj, const ClassTypeInfo* from,
                       std::string_view name, SimContext& ctx,
                       ClassObject** owner) {
  const ClassTypeInfo* declaring = nullptr;
  const ClassMember* member = FindQueuePropertyDecl(from, name, declaring);
  if (member == nullptr) return nullptr;
  if (member->is_static) {
    auto& slot = declaring->static_queue_properties[std::string(name)];
    if (slot == nullptr)
      slot = MakeQueueProperty(declaring, member, nullptr, ctx);
    return slot;
  }
  if (obj == nullptr) return nullptr;
  auto& slot = obj->queue_properties[std::string(name)];
  if (slot == nullptr) slot = MakeQueueProperty(declaring, member, obj, ctx);
  if (owner != nullptr) *owner = obj;
  return slot;
}

// §26.3: the "p.q" key the queue `p::q` names is held under, the key a
// scoped read resolves by (BuildMemberName in eval_expr.cpp) and a package's
// queue is created under; empty for a base of another shape.
std::string PackageQueueKey(const Expr* base) {
  if (base == nullptr || base->kind != ExprKind::kMemberAccess ||
      !base->is_scope_resolution || base->lhs == nullptr ||
      base->rhs == nullptr || base->lhs->kind != ExprKind::kIdentifier ||
      base->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  return std::string(base->lhs->text) + "." + std::string(base->rhs->text);
}

// §8.23: `C::name` names the static property `name` of class C; §26.3:
// `p::q` names the queue package p declares, under its "p.q" key. Resolved
// as a static property alone, `p1::q.push_back(4)` found no class p1 and
// pushed nothing.
QueueObject* ScopeResolvedQueueProperty(const Expr* base, SimContext& ctx) {
  if (base->lhs == nullptr || base->lhs->kind != ExprKind::kIdentifier)
    return nullptr;
  if (auto* q = ctx.FindQueue(PackageQueueKey(base))) return q;
  const ClassTypeInfo* cls = ctx.FindClassType(base->lhs->text);
  if (cls == nullptr) return nullptr;
  return ResolveOn(nullptr, cls, base->rhs->text, ctx, nullptr);
}

}  // namespace

QueueObject* ClassQueueProperty(ClassObject* obj, const ClassTypeInfo* from,
                                std::string_view name, SimContext& ctx) {
  return ResolveOn(obj, from, name, ctx, nullptr);
}

bool InitClassQueueProperty(ClassObject* obj, const ClassTypeInfo* info,
                            std::string_view name, const Expr* init,
                            SimContext& ctx) {
  const ClassTypeInfo* declaring = nullptr;
  const ClassMember* member = FindQueuePropertyDecl(info, name, declaring);
  if (member == nullptr || declaring != info || member->is_static) return false;
  auto& slot = obj->queue_properties[std::string(name)];
  if (slot == nullptr) slot = MakeQueueProperty(info, member, obj, ctx);
  if (init == nullptr) return true;
  // §6.8: each element the initializer gives the queue is storage of its own,
  // so each takes a copy of the words the expression answered with rather
  // than the pointer to them a Logic4Vec copy carries.
  Arena& arena = ctx.GetArena();
  std::vector<Logic4Vec> elems;
  CollectQueueElements(init, ctx, arena, elems);
  for (auto& elem : elems) elem = OwnRhsWords(elem, arena);
  slot->elements = std::move(elems);
  EnforceQueueBound(slot, "initialization", init->range.start, ctx);
  slot->AssignFreshIds();
  ++slot->generation;
  return true;
}

QueueObject* FindQueueOfName(std::string_view name, SimContext& ctx,
                             ClassObject** owner) {
  if (owner != nullptr) *owner = nullptr;
  if (auto* q = ctx.FindQueue(name)) return q;
  // Outside a method there is no class scope to resolve the name in, and this
  // is asked of every element select, so that is settled before the lookups.
  ClassObject* self = ctx.CurrentThis();
  const ClassTypeInfo* from = ctx.CurrentMethodClass();
  if (from == nullptr && self != nullptr) from = self->type;
  if (from == nullptr) return nullptr;
  // A local of the same name is the name's own declaration and shadows the
  // property, so the property is asked for only where no local answers.
  if (ctx.FindVariable(name) != nullptr || ctx.FindArrayInfo(name) != nullptr ||
      ctx.FindAssocArray(name) != nullptr) {
    return nullptr;
  }
  return ResolveOn(self, from, name, ctx, owner);
}

QueueObject* FindQueueOfBase(const Expr* base, SimContext& ctx, Arena& arena,
                             ClassObject** owner) {
  if (owner != nullptr) *owner = nullptr;
  if (base == nullptr) return nullptr;
  // §3.12.1 (printed page 56): `$unit::q.size()` names the unit's queue
  // under "$unit.q" past a module's own q, the key the prefix the parser
  // keeps on the identifier resolves to (DeclaredKindsKey); by the text
  // alone the module's queue answered.
  if (base->kind == ExprKind::kIdentifier)
    return FindQueueOfName(DeclaredKindsKey(base), ctx, owner);
  if (base->kind != ExprKind::kMemberAccess || base->lhs == nullptr ||
      base->rhs == nullptr || base->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  if (base->is_scope_resolution) return ScopeResolvedQueueProperty(base, ctx);
  ClassObject* obj = HandleSideObject(base->lhs, ctx, arena);
  if (obj == nullptr) return nullptr;
  return ResolveOn(obj, obj->type, base->rhs->text, ctx, owner);
}

void AnnounceQueueChange(const Expr* base, ClassObject* owner,
                         SimContext& ctx) {
  if (owner != nullptr) {
    ctx.NotifyClassHandleWatchers(owner->handle);
  } else if (base != nullptr && base->kind == ExprKind::kIdentifier) {
    NotifyOwningVar(ctx, DeclaredKindsKey(base));
  } else if (std::string key = PackageQueueKey(base); !key.empty()) {
    NotifyOwningVar(ctx, key);
  }
}

bool TryEvalQueueElementMember(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  if (expr == nullptr || expr->kind != ExprKind::kMemberAccess ||
      expr->is_scope_resolution || expr->lhs == nullptr ||
      expr->rhs == nullptr || expr->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  const Expr* sel = expr->lhs;
  if (sel->kind != ExprKind::kSelect || sel->base == nullptr ||
      sel->index == nullptr || sel->index_end != nullptr) {
    return false;
  }
  const QueueObject* q = FindQueueOfBase(sel->base, ctx, arena);
  if (q == nullptr || !q->holds_class_handles) return false;
  // The element is read as any select of the queue is (EvalSelect), `$` bound
  // to the last index and an invalid index answering the null handle.
  ClassObject* obj = ctx.GetClassObject(EvalExpr(sel, ctx, arena).ToUint64());
  if (obj == nullptr) return false;
  out = obj->GetProperty(expr->rhs->text, arena);
  return true;
}

}  // namespace delta
