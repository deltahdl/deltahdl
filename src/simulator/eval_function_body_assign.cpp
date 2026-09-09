#include <string>
#include <string_view>

#include "common/arena.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {
// The assignment half of the statement executor for a subroutine body (§13.4):
// how `x = e`, `a[i] = e`, `this.f = e`, `super.f = e` and an unqualified
// property write are performed when they are written inside a function or a
// task. eval_function_body.cpp holds the rest of that executor -- the
// declarations, conditionals and loops -- and calls ExecFuncBlockingAssign at
// the end of this file for every one of these forms.

// True when lhs is a `<base>.<member>` member access whose base identifier name
// matches base_name and whose member is a plain identifier.
static bool IsMemberAccessOn(const Expr* lhs, std::string_view base_name) {
  return lhs->kind == ExprKind::kMemberAccess && lhs->lhs &&
         lhs->lhs->kind == ExprKind::kIdentifier &&
         lhs->lhs->text == base_name && lhs->rhs &&
         lhs->rhs->kind == ExprKind::kIdentifier;
}

// §8.15/§8.18: an unqualified (or `this`-qualified) member write inside a
// method resolves the member in the lexically enclosing class's scope. Routing
// through SetPropertyForType keyed by the current method's class updates the
// scoped storage slot that a later qualified read (`obj.name`, `super.name`, or
// access through a base-typed handle) consults -- so a base constructor that
// runs as part of a chain populates the inherited slot, not just the unscoped
// alias. With no enclosing-class context active, the plain unscoped write is
// preserved, leaving non-method writes unchanged.
// §10.4 puts procedural assignments "within procedures such as always, initial,
// task, and function", so an assignment to a property from a method is one, and
// §10.7 truncates or extends it into the property while §6.11.2 converts the
// unknowns reaching a 2-state one. A Logic4Vec carries its own width, so
// writing the value straight in put the expression's width in the declaration's
// place: §8.2's own `bit [3:0] command;` held eight bits of whatever was
// assigned to it, and its `initiator_id = 5'bx;` held the x.
//
// Only a width the declaration gave is truncated to. CollectClassMembers
// substitutes a 32-bit carrier for a type it could not size, and truncating to
// a carrier would cut a class handle in half and a string down to four
// characters; width_is_declared is what tells the two apart, and it gates the
// state-ness for the same reason.
static void WriteSelfProperty(ClassObject* self, std::string_view name,
                              const Logic4Vec& val, SimContext& ctx,
                              Arena& arena) {
  // §8.11: a `this.x` write updates the invoking instance. Properties are kept
  // under both an unscoped key and a `Type::name` scoped key, and reads consult
  // the scoped key first. In a plain instance method (no enclosing-class
  // context, unlike a constructor) fall back to the object's own type so both
  // copies stay in sync; otherwise the write lands only on the unscoped key and
  // the next read returns the stale scoped value.
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  if (!enclosing) enclosing = self->type;
  Logic4Vec stored = CoerceToPropertyType(enclosing, name, val, arena);
  if (enclosing) {
    self->SetPropertyForType(name, enclosing, stored);
  } else {
    self->SetProperty(std::string(name), stored);
  }
  // §9.4.2: "Changing the value of object data members ... referenced by a
  // method or function shall cause the event expression to be reevaluated".
  // This is the write a method makes to its own object, by `this.f` or by the
  // property's bare name, and it has no variable in hand: the watchers are on
  // whatever variables designate the object, which the handle finds.
  ctx.NotifyClassHandleWatchers(self->handle);
}

// §8.10: a method writes a static property of its enclosing class by
// unqualified reference, mirroring the read path in EvalIdentifier, and §8.11
// has an unqualified name that is not a static property name the instance
// property of the object the method was invoked on. Neither target is one the
// module path knows -- outside a subroutine there is no enclosing class and no
// invoking instance -- so they are answered here, and every other target falls
// to the store §10.4 gives every procedure alike.
//
// Static storage takes precedence over an instance property of the same name.
// A declared local shadows both, and that is the caller's test rather than this
// one's: it asks only for a name no local answers.
static bool TryFuncClassPropertyWrite(const Expr* lhs, const Logic4Vec& val,
                                      SimContext& ctx, Arena& arena) {
  const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
  if (method_cls != nullptr) {
    auto it = method_cls->static_properties.find(std::string(lhs->text));
    if (it != method_cls->static_properties.end()) {
      it->second = val;
      return true;
    }
  }
  auto* self = ctx.CurrentThis();
  if (self == nullptr) return false;
  WriteSelfProperty(self, lhs->text, val, ctx, arena);
  return true;
}

// §8.7: `new` has no type of its own -- "the left-hand side of the assignment
// determines the return type" -- so a bare `new` reaches evaluation with
// nothing to say what to construct, and evaluating it as an ordinary expression
// yields a null handle. Inside a method the left-hand side may be a property of
// the enclosing class rather than a variable, named without a `this.` prefix
// (§8.11); the property's declared class type is then what §8.7 points at, and
// it is resolved from the class the method belongs to. `field_name` is the
// property being written, which is the bare identifier itself or the field of a
// `this.field` target.
//
// Returns false when the target is not a class-handle property, leaving every
// other assignment to the ordinary path.
static bool TrySelfClassNewAssign(const Stmt* stmt, std::string_view field_name,
                                  SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kCall) return false;
  if (stmt->rhs->text != "new") return false;
  auto* self = ctx.CurrentThis();
  if (self == nullptr) return false;
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  if (enclosing == nullptr) enclosing = self->type;
  auto field_type = MemberClassTypeName(enclosing, field_name);
  if (field_type.empty() || ctx.FindClassType(field_type) == nullptr)
    return false;
  WriteSelfProperty(
      self, field_name,
      EvalClassNew(field_type, stmt->rhs, ctx, arena, stmt->rhs->range.start),
      ctx, arena);
  return true;
}

// Run the blocking-assignment handlers that do not need the generic
// right-hand-side value: the three `new` forms and a queue target. Returns
// true when one of them fully handled the assignment.
// §11.4.1 states a compound assignment as one blocking assignment: "an
// assignment operator is semantically equivalent to a blocking assignment, with
// the exception that any left-hand index expression is only evaluated once".
//
// The parser gives `x += 1;` a kBlockingAssign whose lhs is x and whose rhs is
// the compound operator over that same lhs node, so evaluating that rhs reaches
// EvalCompoundAssign, which writes x itself. Handing the value it returned to
// ExecFuncWriteValue then wrote x a second time, and the index the exception
// covers ran again for that write -- a compound assignment written in a
// subroutine body was two assignments, whatever the second one landed on.
// ApplyCompoundAssignOp is the single read-modify-write the ordinary statement
// executor performs, and this reaches it rather than restating it.
//
// A parenthesized rhs is a different statement and is left alone: §11.4.1 lists
// `( operator_assignment )` as a primary, so `x = (y += 2)` assigns x from an
// expression that assigns y, and its target is the rhs's own lhs rather than
// the statement's. TryDispatchSpecialBlockingAssign draws the same line.
static bool TryFuncCompoundAssign(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  if (stmt->rhs == nullptr || stmt->rhs->kind != ExprKind::kBinary ||
      !IsCompoundAssignOp(stmt->rhs->op) || stmt->rhs->is_parenthesized) {
    return false;
  }
  ApplyCompoundAssignOp(stmt, ctx, arena);
  return true;
}

static bool TryFuncSpecialBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                         Arena& arena) {
  if (TryFuncCompoundAssign(stmt, ctx, arena)) return true;
  // §8.4: resolve `new` against the property named on the left before the
  // right-hand side is evaluated without it.
  // A local of the same name shadows the property, so the unqualified form
  // defers to the ordinary variable path when one exists; `this.field` names
  // the property whether or not it is shadowed.
  if (stmt->lhs->kind == ExprKind::kIdentifier &&
      ctx.FindVariable(stmt->lhs->text) == nullptr &&
      TrySelfClassNewAssign(stmt, stmt->lhs->text, ctx, arena))
    return true;
  if (IsMemberAccessOn(stmt->lhs, "this") && stmt->lhs->rhs &&
      TrySelfClassNewAssign(stmt, stmt->lhs->rhs->text, ctx, arena))
    return true;
  // §8.4: `p = new;` where p is a class-typed variable creates an object and
  // stores its handle. TrySelfClassNewAssign above resolves the property forms
  // and declines when the name is a declared local, so an ordinary local
  // handle reaches here; without this it would fall through to the generic
  // right-hand-side evaluation, which reads `new` as a value and leaves the
  // handle null. TryClassNewAssign declines unless the target has a known
  // class type.
  if (TryClassNewAssign(stmt, ctx, arena)) return true;
  // §7.10/§13.4: an assignment to a queue from a function body uses the queue
  // assignment path -- it rebuilds the element list, allocates fresh element
  // ids, and bumps the generation so prior references are outdated -- rather
  // than a flat scalar write that ignores the queue object.
  // TryQueueBlockingAssign guards on an identifier queue target and declines
  // otherwise.
  return TryQueueBlockingAssign(stmt, ctx, arena);
}

// §8's write targets a subroutine body has and no procedure outside one does:
// §8.11's `this.x`, §8.15's `super.x`, and the unqualified reference §8.10 and
// §8.11 give a method over its class's static and instance properties. Returns
// true when the target was one of those and the value was stored.
//
// Everything else is left to the store the module path performs. §10.4 puts
// procedural assignments "within procedures such as always, initial, task, and
// function" and names one set of left-hand sides for all of them, so a
// concatenation target, a streaming target, a select, a whole array and the
// scalar write are the same statements here as there -- and listing them again
// is what left an array assignment, a streaming target and the rest of them
// dropped in silence inside a class method (#3496).
static bool TryFuncClassTargetWrite(const Expr* lhs, const Logic4Vec& val,
                                    SimContext& ctx, Arena& arena) {
  if (IsMemberAccessOn(lhs, "this")) {
    auto* self = ctx.CurrentThis();
    if (self) WriteSelfProperty(self, lhs->rhs->text, val, ctx, arena);
    return true;
  }
  if (IsMemberAccessOn(lhs, "super")) {
    auto* self = ctx.CurrentThis();
    if (self && self->type && self->type->parent) {
      // §8.15's `super.x` names the parent slice, so the width is the one the
      // parent declared. This arm writes the storage directly rather than
      // through WriteSelfProperty, so it asks for the coercion itself.
      self->SetPropertyForType(
          std::string(lhs->rhs->text), self->type->parent,
          CoerceToPropertyType(self->type->parent, lhs->rhs->text, val, arena));
      // §9.4.2 as above: this arm writes the storage directly rather than
      // through WriteSelfProperty, so it announces the change itself.
      ctx.NotifyClassHandleWatchers(self->handle);
    }
    return true;
  }
  // A local of the same name is the name's own declaration and shadows the
  // property, so the property write is asked for only where no local answers.
  if (lhs->kind == ExprKind::kIdentifier &&
      ctx.FindVariable(lhs->text) == nullptr) {
    return TryFuncClassPropertyWrite(lhs, val, ctx, arena);
  }
  return false;
}

// §10.7 opens by making the left-hand side the context for the right-hand
// expression, and §11.6.1 makes a context-determined expression one whose bit
// length "is determined by the bit length of the expression and by the fact
// that it is part of another expression". §11.6 states the consequence for
// addition -- "the bit length of the largest operand, including the left-hand
// side of an assignment, shall be used" -- and gives `logic [16:0] sumB;
// sumB = a + b;` with sixteen-bit operands as the case that keeps the carry.
// Evaluating the right-hand side with no context at all lost that carry inside
// a subroutine while keeping it outside one, because ExecBlockingAssignImpl
// passes the same width and this executor did not.
//
// This is the other half of §10.7 from the resize below it: the resize discards
// bits the expression produced, and the context is what makes the expression
// produce them. Neither implies the other, and a seventeen-bit target now keeps
// seventeen bits of a sixteen-bit sum rather than being handed a truncated one
// to extend.
//
// EvalRhsWithStructContext is what asks for that width outside a subroutine,
// and it is what asks for it here: beside the width it packs a §10.9.2
// structure assignment pattern and a §11.9 tagged expression against the
// target's own layout, so each field expression is coerced to its member's
// width rather than concatenated at its self-determined one. §10.4 gives every
// procedure one set of assignments, so a pattern packed against the union
// member it names in an initial block is packed against it in a method too.
void ExecFuncBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->lhs) return;
  if (TryFuncSpecialBlockingAssign(stmt, ctx, arena)) return;
  // §10.4 names one set of left-hand sides for every procedure, "always,
  // initial, task, and function" alike, so the forms the target's own kind
  // decides are the module path's own dispatch rather than a list restated
  // here. Restating them is what left a whole-array assignment, an assignment
  // pattern, a streaming target, an associative copy, an event alias, a virtual
  // interface bind, an unpacked slice and a subarray write dropped in silence
  // in a class method, which is the only route into a class body.
  //
  // It comes after the four forms above it because those answer for a class
  // context this dispatch has no test for: `new` resolved against a property of
  // the enclosing class, and the compound operator over one.
  if (TryDispatchSpecialBlockingAssign(stmt, ctx, arena)) return;
  // §6.8: "A variable is an abstraction of a data storage element. A variable
  // shall store a value from one assignment to the next." Two variables are two
  // storage elements. No clause has to forbid them sharing one buffer -- the
  // object model the clause describes already makes them separate -- but
  // EvalExpr answers a bare identifier with the source variable's own
  // Logic4Vec, an element select with the element's own, and a Logic4Vec copies
  // its `words` pointer rather than the words. So the store kept the source's
  // buffer, and the `if (!var->is_4state) CoerceTo2State(...)` beside it, an
  // in-place writer, reached back through it: `bit [7:0] y; y = x;` in a task
  // or function body cleared x's own x and z bits in the statement that only
  // read x. The same write outside a subroutine is copied by
  // ExecBlockingAssignImpl; this executor evaluates its own right-hand side and
  // reaches neither of that path's production points.
  //
  // Every store below takes its value from here -- the class property, the
  // struct field, and everything ApplyGenericBlockingAssign writes -- so one
  // copy where the value is produced covers all of them, and no store has to
  // know.
  Logic4Vec val =
      OwnRhsWords(EvalRhsWithStructContext(stmt, ctx, arena), arena);
  if (TryFuncClassTargetWrite(stmt->lhs, val, ctx, arena)) return;
  ApplyGenericBlockingAssign(stmt, val, ctx, arena);
}

}  // namespace delta
