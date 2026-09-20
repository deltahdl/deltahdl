#include "simulator/eval_class_array_handles.h"

#include <cstdint>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_assoc_class_handles.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

namespace {

// The key of the class the elements of the array property `ref` are handles
// of, empty where they are values: the class the property's declared type
// names as written in its declaring class (PropertyClassName), so that
// §8.23's `Outer::Inner kids[2]` in another class and `Inner kids[2]` in
// Outer both answer `Outer::Inner`. A property of a class type has
// width_is_declared false and a 32-bit carrier for its width, so the type is
// the one fact that tells a handle element from a value one. Asked by the
// property record's bare type name, `Outer::Inner kids[2]` held plain
// values: `x.kids[1] = new` constructed nothing and `x.kids[1].v` read 0.
std::string_view ElementClassKey(const ClassArrayRef& ref, SimContext& ctx) {
  return PropertyClassName(ref.obj, ref.obj->type, ref.prop->name, ctx);
}

// `expr` as a single-index select, or null for an expression of any other
// shape.
const Expr* SingleIndexSelect(const Expr* expr) {
  if (expr == nullptr || expr->kind != ExprKind::kSelect ||
      expr->base == nullptr || expr->index == nullptr ||
      expr->index_end != nullptr) {
    return nullptr;
  }
  return expr;
}

// `expr` as `<select>.name`, a member access that is no scope resolution on a
// single-index select, answering the select; null for any other shape.
const Expr* SelectOfMemberAccess(const Expr* expr) {
  if (expr == nullptr || expr->kind != ExprKind::kMemberAccess ||
      expr->is_scope_resolution || expr->rhs == nullptr ||
      expr->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  return SingleIndexSelect(expr->lhs);
}

// §8.4 with §7.4.2 (printed pages 153-154) and §7.5 (printed 157): the key
// of the class the elements of the declared array `base` names are handles
// of, empty where `base` is no bare name of a fixed-size or dynamic array the
// run holds a shape for, or the array's declaration recorded no class. The
// declaration records the element class under the array's name as it does
// for a variable of a class type (SetVariableClassType by Lowerer::LowerVar
// for a module's, ExecVarDeclImpl for a block's, CreateFuncLocalVar for a
// subroutine body's), so the name is what tells an array of handles from one
// of values, as HandleArrayOfSelect (eval_assoc_class_handles.cpp) reads it
// for an associative array. A queue's elements are told by the queue's own
// flag (TryEvalQueueElementMember) and are not asked for here.
std::string_view DeclaredArrayElementClass(const Expr* base, SimContext& ctx) {
  if (base == nullptr || base->kind != ExprKind::kIdentifier ||
      ctx.FindArrayInfo(base->text) == nullptr) {
    return {};
  }
  std::string_view cls = ctx.GetVariableClassType(base->text);
  return ctx.FindClassType(cls) != nullptr ? cls : std::string_view{};
}

// §8.4: `a[i] = new` where `a` is a declared array of handles: the element's
// declared class is constructed and the handle written into the element as
// any value is (TrySelectBlockingAssign: the element variable of a
// fixed-size array, the queue-backed element of a dynamic one), an index
// addressing no element writing nothing (§7.4.6). Before this the statement
// had no path: TryClassNewAssign (statement_assign_object.cpp) takes a bare
// name or `p::h` for its target and the constructors here served array
// properties alone, so `arr[0] = new` on a module's or a block's `C arr[2]`
// fell to the generic assignment, which reads `new` as a value and
// constructed nothing.
bool TryDeclaredArrayElementNew(const Expr* lhs, const Expr* rhs,
                                SimContext& ctx, Arena& arena) {
  std::string_view cls = DeclaredArrayElementClass(lhs->base, ctx);
  if (cls.empty()) return false;
  Logic4Vec handle = ConstructElementObject(rhs, cls, ctx, arena);
  TrySelectBlockingAssign(lhs, handle, ctx, arena);
  return true;
}

// The property `field` of the object the element `sel` refers to, the element
// read as any select of its array is -- an index addressing no element
// answering the element type's default, which is the null handle -- and
// false for a null handle.
bool ReadElementObjectProperty(const Expr* sel, std::string_view field,
                               SimContext& ctx, Arena& arena, Logic4Vec& out) {
  ClassObject* obj = ctx.GetClassObject(EvalExpr(sel, ctx, arena).ToUint64());
  if (obj == nullptr) return false;
  out = obj->GetProperty(field, arena);
  return true;
}

// §8.4/§7.4.2: `a[i].v` where `a` is a declared array of handles, the
// property `v` of the object the element refers to. Before this the read had
// no path: the member name EvalMemberAccess builds from the expression
// flattens no select, so `arr[0].v` named no variable and read 0.
bool TryEvalDeclaredArrayElementMember(const Expr* expr, SimContext& ctx,
                                       Arena& arena, Logic4Vec& out) {
  const Expr* sel = SelectOfMemberAccess(expr);
  if (sel == nullptr || DeclaredArrayElementClass(sel->base, ctx).empty())
    return false;
  return ReadElementObjectProperty(sel, expr->rhs->text, ctx, arena, out);
}

}  // namespace

Logic4Vec ConstructElementObject(const Expr* rhs, std::string_view class_type,
                                 SimContext& ctx, Arena& arena) {
  if (rhs->lhs != nullptr && rhs->lhs->kind == ExprKind::kIdentifier) {
    auto* src = ctx.GetClassObject(EvalExpr(rhs->lhs, ctx, arena).ToUint64());
    if (src != nullptr) {
      return MakeLogic4VecVal(arena, 64,
                              ctx.AllocateClassObject(src->ShallowCopy(arena)));
    }
  }
  return EvalClassNew(class_type, rhs, ctx, arena, rhs->range.start);
}

bool TryClassArrayElementNewAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  const Expr* lhs = SingleIndexSelect(stmt->lhs);
  const Expr* rhs = stmt->rhs;
  if (lhs == nullptr || rhs == nullptr || rhs->kind != ExprKind::kCall ||
      rhs->text != "new") {
    return false;
  }
  if (TryDeclaredArrayElementNew(lhs, rhs, ctx, arena)) return true;
  ClassArrayRef ref;
  if (!ResolveClassArray(lhs->base, ctx, arena, ref)) return false;
  std::string_view class_key = ElementClassKey(ref, ctx);
  if (class_key.empty()) return false;
  // §11.4.1: the index is evaluated once, before the constructor runs, which
  // may write the array itself.
  Logic4Vec idx_val = EvalExpr(lhs->index, ctx, arena);
  if (HasUnknownBits(idx_val)) return true;
  int64_t index = SelectBoundValue(idx_val);
  if (index < ref.lo || index >= ref.lo + static_cast<int64_t>(ref.size))
    return true;
  Logic4Vec handle = ConstructElementObject(rhs, class_key, ctx, arena);
  ref.obj->SetProperty(ClassArrayElementKey(ref.prop->name, index), handle);
  // §9.4.2: a change to an object's data member wakes a process waiting on
  // the object, as every other write to an element of the property tells it.
  ctx.NotifyClassHandleWatchers(ref.obj->handle);
  return true;
}

bool TryEvalClassArrayElementMember(const Expr* expr, SimContext& ctx,
                                    Arena& arena, Logic4Vec& out) {
  const Expr* sel = SelectOfMemberAccess(expr);
  if (sel == nullptr) return false;
  ClassArrayRef ref;
  if (!ResolveClassArray(sel->base, ctx, arena, ref) ||
      ElementClassKey(ref, ctx).empty()) {
    return false;
  }
  // The element is read as any select of the property is (EvalSelect through
  // TryClassArrayElementSelect).
  return ReadElementObjectProperty(sel, expr->rhs->text, ctx, arena, out);
}

bool TryEvalElementObjectMember(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  return TryEvalQueueElementMember(expr, ctx, arena, out) ||
         TryEvalDeclaredArrayElementMember(expr, ctx, arena, out) ||
         TryEvalClassArrayElementMember(expr, ctx, arena, out) ||
         TryEvalAssocElementMember(expr, ctx, arena, out);
}

// Whether the element `sel` selects is a handle: of a declared fixed-size or
// dynamic array (DeclaredArrayElementClass), or of a queue flagged as holding
// handles, declared or a property (FindQueueOfBase). `declared` receives the
// class the element is declared of -- the array's, or the one a declared
// queue's declaration recorded under its name -- and stays empty for a queue
// property, whose element is then dispatched by its object's own class.
static bool SelectsAHandleElement(const Expr* sel, SimContext& ctx,
                                  Arena& arena, std::string_view& declared) {
  declared = DeclaredArrayElementClass(sel->base, ctx);
  if (!declared.empty()) return true;
  const QueueObject* q = FindQueueOfBase(sel->base, ctx, arena);
  if (q == nullptr || !q->holds_class_handles) return false;
  if (sel->base->kind == ExprKind::kIdentifier)
    declared = ctx.GetVariableClassType(sel->base->text);
  return true;
}

bool TryEvalElementObjectMethodCall(const Expr* expr, SimContext& ctx,
                                    Arena& arena, Logic4Vec& out) {
  if (expr == nullptr || expr->kind != ExprKind::kCall) return false;
  const Expr* sel = SelectOfMemberAccess(expr->lhs);
  std::string_view declared;
  if (sel == nullptr || !SelectsAHandleElement(sel, ctx, arena, declared))
    return false;
  // The element is read as any select of its container is, an index
  // addressing no element answering the null handle, which resolves no
  // method.
  ClassObject* obj = ctx.GetClassObject(EvalExpr(sel, ctx, arena).ToUint64());
  InstanceMethodInfo info;
  if (!ResolveMethodByDeclaredClass(obj, declared, expr->lhs->rhs->text, ctx,
                                    info)) {
    return false;
  }
  out = RunInstanceMethod(info, expr, ctx, arena);
  return true;
}

}  // namespace delta
