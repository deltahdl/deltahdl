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
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/declared_class_key.h"
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

// §8.5/§7.10: the one unpacked dimension of the property declaration `member`
// of `declaring` where it is a queue dimension, written `[$]` or `[$:N]`
// (Syntax 7-4) on the declaration or, §7.4.4 (printed page 155), on the
// typedef its type names (PropertyTypedefItem); null where the property is no
// queue.
const Expr* QueuePropertyDim(const ClassMember* member,
                             const ClassTypeInfo* declaring, SimContext& ctx) {
  if (member->is_param) return nullptr;
  const ModuleItem* item = PropertyTypedefItem(member, declaring, ctx);
  const std::vector<Expr*>& dims =
      item != nullptr ? item->unpacked_dims : member->unpacked_dims;
  if (dims.size() != 1 || !IsQueueDim(dims[0])) return nullptr;
  return dims[0];
}

// §8.5/§7.10: the declaration of the property `name` on the class chain from
// `type` whose one unpacked dimension is a queue dimension, and the class
// that declares it in `declaring`. The nearest declaration is the one that
// answers (§8.13): a class between that redeclares the name as something else
// hides the queue below it, and answers null.
const ClassMember* FindQueuePropertyDecl(const ClassTypeInfo* type,
                                         std::string_view name, SimContext& ctx,
                                         const ClassTypeInfo*& declaring) {
  for (const auto* t = type; t != nullptr; t = t->parent) {
    if (t->decl == nullptr) continue;
    for (const auto* member : t->decl->members) {
      if (member->kind != ClassMemberKind::kProperty || member->name != name)
        continue;
      if (QueuePropertyDim(member, t, ctx) == nullptr) return nullptr;
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

// §8.4: whether the element type of the property `member` of `declaring` on
// `obj` is a class, so that each element is a handle: the type the
// declaration names -- the typedef's element type where a typedef gives the
// property its dimension (PropertyTypedefItem) -- or, where it names a type
// parameter (§8.25), the type the object's specialization binds that parameter
// to, else the default the class declares, as §8.26's `T myFifo[$:DEPTH-1]` on
// a `Fifo#(Item)`. §8.23 (printed pages 200-201): a nested class is named
// `Outer::Inner` from outside its container and bare within it, the key
// DeclaredClassKeyInScope (declared_class_key.h) resolves the written type to;
// asked by the bare `Inner` alone, `Outer::Inner q[$]` was a queue of plain
// values and `h.q[0].v` read 0. A type written as a bare identifier expression,
// which carries no type_name, is still asked for by that name.
bool ElementTypeIsClass(const ClassMember* member,
                        const ClassTypeInfo* declaring, const ClassObject* obj,
                        SimContext& ctx) {
  const ClassDecl* decl = declaring->decl;
  const ModuleItem* item = PropertyTypedefItem(member, declaring, ctx);
  const DataType* type =
      item != nullptr ? &item->typedef_type : &member->data_type;
  std::string_view name = TypeNameOf(*type);
  if (name.empty()) return false;
  if (decl->type_param_names.count(name) != 0) {
    type = TypeParamActual(obj, decl, name);
    if (type == nullptr) return false;
    name = TypeNameOf(*type);
  }
  if (!DeclaredClassKeyInScope(*type, declaring, ctx, ctx.GetArena()).empty())
    return true;
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
  q->max_size =
      PropertyQueueBound(QueuePropertyDim(member, declaring, ctx), obj, ctx);
  q->holds_class_handles = ElementTypeIsClass(member, declaring, obj, ctx);
  return q;
}

// The queue ClassQueueProperty answers, with `owner` set to the object whose
// property it is, or to null for a static property's, which no object owns.
QueueObject* ResolveOn(ClassObject* obj, const ClassTypeInfo* from,
                       std::string_view name, SimContext& ctx,
                       ClassObject** owner) {
  const ClassTypeInfo* declaring = nullptr;
  const ClassMember* member = FindQueuePropertyDecl(from, name, ctx, declaring);
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

// §8.9 with §8.23 and §26.3: the class the scope resolution `base` names a
// static property of, and in `member` the property: `C::all` names class C's,
// and `p::C::all` names the class package p declares, which the lowerer binds
// under "p::C" and PackageQualifiedClassOf answers. Null for a base of any
// other shape or a name that is no class's, a package's own `p::q` included.
// Read as `C::all` alone, `p::C::all.push_back(5)` found no class named
// `p::C::all`'s left and pushed nothing, its size() answering 0.
const ClassTypeInfo* ScopeResolvedClass(const Expr* base, SimContext& ctx,
                                        std::string_view& member) {
  if (base->lhs == nullptr) return nullptr;
  if (base->lhs->kind == ExprKind::kMemberAccess)
    return PackageQualifiedClassOf(base, ctx, member);
  if (base->lhs->kind != ExprKind::kIdentifier) return nullptr;
  member = base->rhs->text;
  return ctx.FindClassType(base->lhs->text);
}

// §8.23: `C::name` names the static property `name` of class C, and §26.3's
// `p::C::name` the one of a package's class; §26.3: `p::q` names the queue
// package p declares, under its "p.q" key. Resolved as a static property
// alone, `p1::q.push_back(4)` found no class p1 and pushed nothing.
QueueObject* ScopeResolvedQueueProperty(const Expr* base, SimContext& ctx) {
  if (auto* q = ctx.FindQueue(PackageQueueKey(base))) return q;
  std::string_view member;
  const ClassTypeInfo* cls = ScopeResolvedClass(base, ctx, member);
  if (cls == nullptr) return nullptr;
  return ResolveOn(nullptr, cls, member, ctx, nullptr);
}

// §8.10 and §8.11: the class a bare name inside a method is resolved in --
// the running method's class, or the object's own where no method class is
// in force -- and null outside a method, where there is no class scope to
// resolve the name in.
const ClassTypeInfo* MethodScopeClass(SimContext& ctx) {
  const ClassTypeInfo* from = ctx.CurrentMethodClass();
  ClassObject* self = ctx.CurrentThis();
  if (from == nullptr && self != nullptr) from = self->type;
  return from;
}

// A local of the same name is the name's own declaration and shadows a
// property, so a property is asked for only where no local answers.
bool LocalShadowsProperty(std::string_view name, SimContext& ctx) {
  return ctx.FindVariable(name) != nullptr ||
         ctx.FindArrayInfo(name) != nullptr ||
         ctx.FindAssocArray(name) != nullptr;
}

// §8.9 (printed page 186): the class whose own storage holds the static queue
// property `base` names -- `C::all` or `p::C::all` through the scope operator,
// or the bare `all` a method of C names (§8.10), where no declared queue or
// local of the name shadows it, resolved as FindQueueOfName resolves the
// name -- else null. §8.13 (printed 189-190): that is the declaring class,
// C for `D::all` and for the bare `all` of D's own method where D extends C,
// which FindQueuePropertyDecl walks the extends chain to, and which the
// watchers of `wait (D::all.size() != 0)` are armed on. What names a static
// property is the class, not an object, so this is what AnnounceQueueChange
// tells §9.4.2's watchers through where FindQueueOfBase gave it no owner.
const ClassTypeInfo* StaticQueuePropertyClass(const Expr* base,
                                              SimContext& ctx) {
  const ClassTypeInfo* from = nullptr;
  std::string key;
  std::string_view name;
  if (base->kind == ExprKind::kIdentifier) {
    key = DeclaredKindsKey(base);
    name = key;
    if (ctx.FindQueue(name) != nullptr || LocalShadowsProperty(name, ctx))
      return nullptr;
    from = MethodScopeClass(ctx);
  } else if (base->kind == ExprKind::kMemberAccess &&
             base->is_scope_resolution && base->rhs != nullptr &&
             base->rhs->kind == ExprKind::kIdentifier) {
    from = ScopeResolvedClass(base, ctx, name);
  }
  if (from == nullptr) return nullptr;
  const ClassTypeInfo* declaring = nullptr;
  const ClassMember* member = FindQueuePropertyDecl(from, name, ctx, declaring);
  return member != nullptr && member->is_static ? declaring : nullptr;
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
  const ClassMember* member = FindQueuePropertyDecl(info, name, ctx, declaring);
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
  const ClassTypeInfo* from = MethodScopeClass(ctx);
  if (from == nullptr || LocalShadowsProperty(name, ctx)) return nullptr;
  return ResolveOn(ctx.CurrentThis(), from, name, ctx, owner);
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

// §9.4.3 (printed page 236) with §8.9 (printed 186): a static queue property
// is the class's own storage, one for every object and for no object at all,
// which no object's watchers see written and no variable's name stands for,
// so its change is told to the class's static watchers -- those
// AnyChangeAwaiter::AttachStaticPropertyWatcher (awaiters.h) arms a wait on
// `C::all.size()`, `p::C::all.size()` or a static method's bare `all.size()`
// on -- as every write to a static value property is
// (ClassTypeInfo::NotifyStaticWatchers). With `owner` null and the base no
// declared queue's name, `C::all.push_back(7)` announced nothing, and the
// wait stayed parked for ever.
void AnnounceQueueChange(const Expr* base, ClassObject* owner,
                         SimContext& ctx) {
  if (owner != nullptr) {
    ctx.NotifyClassHandleWatchers(owner->handle);
    return;
  }
  if (base == nullptr) return;
  if (const ClassTypeInfo* cls = StaticQueuePropertyClass(base, ctx)) {
    cls->NotifyStaticWatchers();
  } else if (base->kind == ExprKind::kIdentifier) {
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
