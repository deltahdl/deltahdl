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
#include "simulator/eval_array_element_queue.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/eval_member_path.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/queue_bound.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

namespace {

const Expr* QueuePropertyDim(const ClassMember* member,
                             const ClassTypeInfo* declaring, SimContext& ctx) {
  if (member->is_param) return nullptr;
  const ModuleItem* item = PropertyTypedefItem(member, declaring, ctx);
  const std::vector<Expr*>& dims =
      item != nullptr ? item->unpacked_dims : member->unpacked_dims;
  if (dims.size() != 1 || !IsQueueDim(dims[0])) return nullptr;
  return dims[0];
}

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

std::string_view TypeNameOf(const DataType& type) {
  if (!type.type_name.empty()) return type.type_name;
  if (type.type_ref_expr != nullptr &&
      type.type_ref_expr->kind == ExprKind::kIdentifier) {
    return type.type_ref_expr->text;
  }
  return {};
}

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

QueueObject* MakeQueueProperty(const ClassTypeInfo* declaring,
                               const ClassMember* member, ClassObject* obj,
                               SimContext& ctx) {
  const auto* prop = declaring->FindProperty(member->name);
  auto* q = ctx.GetArena().Create<QueueObject>();
  q->elem_width = prop == nullptr ? 32 : prop->is_string ? 0 : prop->width;
  q->is_4state = prop != nullptr && prop->is_4state;
  q->is_signed = prop != nullptr && prop->is_signed;
  q->max_size =
      PropertyQueueBound(QueuePropertyDim(member, declaring, ctx), obj, ctx);
  q->holds_class_handles = ElementTypeIsClass(member, declaring, obj, ctx);
  return q;
}

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

std::string PackageQueueKey(const Expr* base) {
  if (base == nullptr || base->kind != ExprKind::kMemberAccess ||
      !base->is_scope_resolution || base->lhs == nullptr ||
      base->rhs == nullptr || base->lhs->kind != ExprKind::kIdentifier ||
      base->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  return std::string(base->lhs->text) + "." + std::string(base->rhs->text);
}

const ClassTypeInfo* ScopeResolvedClass(const Expr* base, SimContext& ctx,
                                        std::string_view& member) {
  if (base->lhs == nullptr) return nullptr;
  if (base->lhs->kind == ExprKind::kMemberAccess)
    return PackageQualifiedClassOf(base, ctx, member);
  if (base->lhs->kind != ExprKind::kIdentifier) return nullptr;
  member = base->rhs->text;
  return ctx.FindClassType(base->lhs->text);
}

QueueObject* ScopeResolvedQueueProperty(const Expr* base, SimContext& ctx) {
  if (auto* q = ctx.FindQueue(PackageQueueKey(base))) return q;
  std::string_view member;
  const ClassTypeInfo* cls = ScopeResolvedClass(base, ctx, member);
  if (cls == nullptr) return nullptr;
  return ResolveOn(nullptr, cls, member, ctx, nullptr);
}

const ClassTypeInfo* MethodScopeClass(SimContext& ctx) {
  const ClassTypeInfo* from = ctx.CurrentMethodClass();
  ClassObject* self = ctx.CurrentThis();
  if (from == nullptr && self != nullptr) from = self->type;
  return from;
}

bool LocalShadowsProperty(std::string_view name, SimContext& ctx) {
  return ctx.FindVariable(name) != nullptr ||
         ctx.FindArrayInfo(name) != nullptr ||
         ctx.FindAssocArray(name) != nullptr;
}

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

bool IsQueuePropertyDecl(const ClassMember* member,
                         const ClassTypeInfo* declaring, SimContext& ctx) {
  return QueuePropertyDim(member, declaring, ctx) != nullptr;
}

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
  const ClassTypeInfo* from = MethodScopeClass(ctx);
  if (from == nullptr || LocalShadowsProperty(name, ctx)) return nullptr;
  return ResolveOn(ctx.CurrentThis(), from, name, ctx, owner);
}

static QueueObject* MethodResultQueue(const Expr* base, SimContext& ctx,
                                      Arena& arena) {
  const bool kCallForm = base->kind == ExprKind::kCall;
  const bool kWithForm =
      base->kind == ExprKind::kMemberAccess && base->with_expr != nullptr;
  if (!kCallForm && !kWithForm) return nullptr;
  std::vector<Logic4Vec> elems;
  if (!TryCollectLocatorResult(base, ctx, arena, elems)) return nullptr;
  auto* q = arena.Create<QueueObject>();
  q->elem_width = elems.empty() ? 32 : elems.front().width;
  q->is_signed = !elems.empty() && elems.front().is_signed;
  q->elements = std::move(elems);
  q->AssignFreshIds();
  return q;
}

QueueObject* FindWrittenQueueOfBase(const Expr* base, SimContext& ctx,
                                    Arena& arena, ClassObject** owner) {
  if (base == nullptr || base->kind != ExprKind::kSelect) {
    if (QueueObject* member = ResolveStructDynMember(base, ctx, arena, true)) {
      if (owner != nullptr) *owner = nullptr;
      return member;
    }
    return FindQueueOfBase(base, ctx, arena, owner);
  }
  if (owner != nullptr) *owner = nullptr;
  return ElementQueueOfSelect(base, ctx, arena, true);
}

QueueObject* FindQueueOfBase(const Expr* base, SimContext& ctx, Arena& arena,
                             ClassObject** owner) {
  if (owner != nullptr) *owner = nullptr;
  if (base == nullptr) return nullptr;
  if (base->kind == ExprKind::kIdentifier)
    return FindQueueOfName(DeclaredKindsKey(base), ctx, owner);
  if (base->kind == ExprKind::kSelect)
    return ElementQueueOfSelect(base, ctx, arena, false);
  if (QueueObject* result = MethodResultQueue(base, ctx, arena)) return result;
  if (base->kind != ExprKind::kMemberAccess || base->lhs == nullptr ||
      base->rhs == nullptr || base->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  if (base->is_scope_resolution) return ScopeResolvedQueueProperty(base, ctx);
  if (QueueObject* member = ResolveStructDynMember(base, ctx, arena, false)) {
    return member;
  }
  ClassObject* obj = HandleSideObject(base->lhs, ctx, arena);
  if (obj == nullptr) return ctx.FindQueue(InstanceMemberKey(base));
  return ResolveOn(obj, obj->type, base->rhs->text, ctx, owner);
}

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
  ClassObject* obj = ctx.GetClassObject(EvalExpr(sel, ctx, arena).ToUint64());
  if (obj == nullptr) return false;
  out = obj->GetProperty(expr->rhs->text, arena);
  return true;
}

static QueueObject* ClassArrayElementsCopy(const Expr* receiver,
                                           SimContext& ctx, Arena& arena) {
  ClassArrayRef ref;
  if (!ResolveClassArray(receiver, ctx, arena, ref) || ref.lo != 0 ||
      ref.prop->array_descending) {
    return nullptr;
  }
  auto* q = arena.Create<QueueObject>();
  q->elem_width = ref.prop->width;
  q->is_4state = ref.prop->is_4state;
  for (uint32_t i = 0; i < ref.size; ++i)
    q->elements.push_back(ReadClassArrayElement(ref, i, ctx, arena));
  q->AssignFreshIds();
  return q;
}

static std::string_view ReceiverQueueName(const Expr* receiver, Arena& arena) {
  if (receiver->kind == ExprKind::kIdentifier) return receiver->text;
  if (receiver->kind == ExprKind::kCall) return "$method.result";
  if (receiver->kind == ExprKind::kSelect) return "$subarray";
  return *arena.Create<std::string>(FlattenHierPath(receiver));
}

QueuePropertyReceiver::QueuePropertyReceiver(const Expr* call, SimContext& ctx,
                                             Arena& arena)
    : ctx_(ctx) {
  const Expr* access =
      call != nullptr && call->kind == ExprKind::kCall ? call->lhs : call;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution || access->lhs == nullptr) {
    return;
  }
  const Expr* receiver = access->lhs;
  const bool kBare = receiver->kind == ExprKind::kIdentifier;
  const bool kCall = receiver->kind == ExprKind::kCall;
  const bool kSubarray = receiver->kind == ExprKind::kSelect;
  if (kBare
          ? ctx.FindQueue(receiver->text) != nullptr
          : receiver->kind != ExprKind::kMemberAccess && !kCall && !kSubarray) {
    return;
  }
  QueueObject* q = kSubarray ? nullptr : FindQueueOfBase(receiver, ctx, arena);
  if (q == nullptr) q = ClassArrayElementsCopy(receiver, ctx, arena);
  if (q == nullptr) return;
  std::string_view name = ReceiverQueueName(receiver, arena);
  ctx.PushScope();
  std::vector<Scope> stack = ctx.SwapScopeStack({});
  stack.back().queues[name] = q;
  ctx.SwapScopeStack(std::move(stack));
  auto* bare = arena.Create<Expr>();
  bare->kind = ExprKind::kIdentifier;
  bare->text = name;
  bare->range = receiver->range;
  auto* renamed = arena.Create<Expr>(*access);
  renamed->lhs = bare;
  if (access == call) {
    call_ = renamed;
    return;
  }
  auto* renamed_call = arena.Create<Expr>(*call);
  renamed_call->lhs = renamed;
  call_ = renamed_call;
}

QueuePropertyReceiver::~QueuePropertyReceiver() {
  if (call_ != nullptr) ctx_.PopScope();
}

}  // namespace delta
