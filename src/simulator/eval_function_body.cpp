#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_exec.h"

namespace delta {
// The statement executor for a subroutine body (13.4). A function or task
// body does not run on the scheduler the way a procedural block does: it runs
// to completion within the caller's evaluation, so it needs its own execution
// of every statement form -- assignments, declarations, conditionals and
// loops -- that returns as soon as a `return` is reached. Those live here;
// eval_function_args.cpp holds the argument binding and write-back that
// surround a call.

// §10.4 lists "Bit-selects, part-selects, and slices of packed arrays" among
// the left-hand sides a procedural assignment may take, and puts such
// assignments "within procedures such as always, initial, task, and function",
// so a select target inside a subroutine body names the same things it names
// outside one. This looked for an element variable named `a[i]` and nothing
// else, so of the forms §11.5.1 defines only an unpacked array element was
// reached: a bit-select of a packed variable built the name `v[2]`, which no
// variable answers to, and wrote nothing, and a part-select built its name from
// the msb expression alone and wrote nothing either. Neither was reported.
//
// What it did write, it wrote whole. A Logic4Vec carries its own width, so
// `elem->value = val` put the value's width in the element's place rather than
// truncating into it, which is the §10.7 defect 820f37a1e fixed at the
// identifier arm and left here because a select's width is its own question.
//
// TrySelectBlockingAssign is what the assignment outside a subroutine asks, and
// it asks it of every form at once: an unpacked array element resized to the
// element's width, a queue or associative element by its own writer, the bits
// an associative element's select names, a compound `a[i][j]`, the byte a
// string's index names (§6.16), and otherwise WriteBitSelect, which deposits
// the value into the window the select opened and leaves the rest of the
// variable standing. The associative-array key rules §7.8.1, §7.8.4 and §7.8.6
// decide still reach it, TryAssocIndexedWrite being one of the writers it
// dispatches to, so `aa[-1] = v` still reaches the entry the same statement
// reaches among a module's items rather than a second entry of its own.
static void ExecFuncSelectAssign(const Expr* lhs, const Logic4Vec& val,
                                 SimContext& ctx, Arena& arena) {
  Logic4Vec rhs_val = val;
  TrySelectBlockingAssign(lhs, rhs_val, ctx, arena);
}

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
}

// Assigns to a plain identifier lhs: writes the local variable when present,
// otherwise falls back to a property on the current `this` object.
//
// §10.7: "the MSBs of the right-hand expression shall be discarded to match the
// size of the left-hand side", and a right-hand side narrower than the target
// is padded to it. A Logic4Vec carries its own width, so writing the value over
// the variable put the expression's width in the variable's place instead and
// truncated nothing: the `a = 8'hff` of §10.7's Example 1 left a six-bit `a`
// eight bits wide reading 255 rather than 6'h3f. The same statement outside a
// subroutine has always been resized, by AssignToScalarLhs in
// statement_assign_core.cpp; a subroutine body runs on its own statement
// executor and so has to be told the same rule separately.
//
// ConvertRealOnAssign is the resize, and carries §6.12.1's real conversion with
// it, which a target registered as real needs before its bits mean anything.
//
// §6.16 gives a string no declared width for a value to be resized to -- it is
// as long as what it holds -- so a string target keeps the value it was handed.
// A string local is marked as one where it is created, without which this would
// read its width from whatever it was last assigned and truncate every later
// assignment to the length of the first.
static void ExecFuncIdentifierAssign(const Expr* lhs, const Logic4Vec& val,
                                     SimContext& ctx, Arena& arena) {
  auto* var = ctx.FindVariable(lhs->text);
  if (var) {
    // §10.6.2: "A force statement to a variable shall override a procedural
    // assignment, continuous assignment or an assign procedural continuous
    // assignment to the variable until a release procedural statement is
    // executed on the variable." §10.4 puts procedural assignments "within
    // procedures such as always, initial, task, and function", so an assignment
    // written in a subroutine body is one of the assignments a force overrides,
    // and this executor consulted the flag nowhere. AssignToScalarLhs declines
    // on the same test outside a subroutine. A release clears the flag and
    // leaves the value standing, so the next assignment through here lands.
    if (var->is_forced) return;
    if (var->is_string) {
      var->value = val;
    } else {
      var->value = ConvertRealOnAssign(val, lhs, var->value.width, ctx, arena);
      // §6.11.2: "When a 4-state value is automatically converted to a 2-state
      // value, any unknown or high-impedance bits shall be converted to zeros."
      // AssignToScalarLhs converts on the same test outside a subroutine, and
      // this executor converted nowhere, so an x assigned to a `bit` or an
      // `int` in a task or function body survived as an x.
      if (!var->is_4state) CoerceTo2State(var->value);
    }
    // §9.4.2: "A non-edge implicit event shall be detected on any change in the
    // value of the expression", and the subclause names a subroutine as the
    // writer where it requires that "Changing the value of object data members,
    // aggregate elements, or the size of a dynamically sized array referenced
    // by a method or function shall cause the event expression to be
    // reevaluated". A watcher is the only route by which a process parked on
    // @(x), wait(x) or an always_comb's inferred sensitivity list is resumed,
    // and this executor notified none: a module-scope variable, or a caller's
    // variable reached through a `ref` formal, written from a function body
    // left every process waiting on it parked for the rest of the run. The
    // notification is unconditional, whether a given change counts being the
    // awaiter's own test -- AnyChangeAwaiter::ChangeGatePasses and
    // EventAwaiter::CheckEdge each decline a wake on a value that did not
    // change. It sits behind the is_forced return because a variable that
    // declines the store declines the notification with it, as WriteVar and
    // WriteBitSelect both do.
    var->NotifyWatchers();
    return;
  }
  // §8.10: a static method writes a static property of the enclosing class by
  // unqualified reference (mirrors the read path in EvalIdentifier). Static
  // storage takes precedence over an instance property of the same name.
  const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
  if (method_cls) {
    auto it = method_cls->static_properties.find(std::string(lhs->text));
    if (it != method_cls->static_properties.end()) {
      it->second = val;
      return;
    }
  }
  auto* self = ctx.CurrentThis();
  if (self) WriteSelfProperty(self, lhs->text, val, ctx, arena);
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

// Write an already-evaluated value to the target the left-hand side names.
static void ExecFuncWriteValue(const Expr* lhs, const Logic4Vec& val,
                               SimContext& ctx, Arena& arena) {
  // §11.4.12: "The concatenation is treated as a packed vector of bits. It can
  // be used on the left-hand side of an assignment", the clause's own example
  // being `{log1, log2, log3} = 3'b111;`. §10.4 puts procedural assignments
  // "within procedures such as always, initial, task, and function", so that is
  // as true in a subroutine body as outside one -- and this function named no
  // concatenation form at all, so such an assignment wrote nothing and reported
  // nothing. TryUnpackConcatLhs is what the assignment outside a subroutine
  // asks, and it answers for §10.9's assignment-pattern target as well.
  if (TryUnpackConcatLhs(lhs, val, ctx, arena)) return;
  if (lhs->kind == ExprKind::kIdentifier) {
    ExecFuncIdentifierAssign(lhs, val, ctx, arena);
    return;
  }
  if (lhs->kind == ExprKind::kSelect) {
    ExecFuncSelectAssign(lhs, val, ctx, arena);
    return;
  }
  if (IsMemberAccessOn(lhs, "this")) {
    auto* self = ctx.CurrentThis();
    if (self) WriteSelfProperty(self, lhs->rhs->text, val, ctx, arena);
    return;
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
    }
    return;
  }
  // §8.4: a member access whose base is neither `this` nor `super` names a
  // field of whatever the base denotes -- an object reached through a handle
  // variable, a static class property, or a struct field. The two branches
  // above cover only the enclosing object, so without this a write such as
  // `p.x = 42` through an ordinary handle would be dropped silently. The
  // shared writer resolves the base and performs the write for every one of
  // those forms.
  if (lhs->kind == ExprKind::kMemberAccess) {
    WriteStructField(lhs, val, ctx);
  }
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
// LhsContextWidth alone, rather than the EvalRhsWithStructContext that wraps it
// outside a subroutine: that function also packs a §10.9.2 assignment pattern
// and a §11.9 tagged expression against the target's layout, which are claims
// of their own about clauses this is not.
static void ExecFuncBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  if (!stmt->lhs) return;
  if (TryFuncSpecialBlockingAssign(stmt, ctx, arena)) return;
  uint32_t ctx_width = LhsContextWidth(stmt->lhs, ctx, arena);
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
  // Every store below takes its value from here -- the identifier arm, the
  // string arm beside it, the select writers behind TrySelectBlockingAssign,
  // the class property and the struct field -- so one copy where the value is
  // produced covers all of them, and no store has to know.
  Logic4Vec val =
      OwnRhsWords(EvalExpr(stmt->rhs, ctx, arena, ctx_width), arena);
  ExecFuncWriteValue(stmt->lhs, val, ctx, arena);
}

// The environment in which a subroutine body executes (§13.4): the return
// variable that a `return` writes, the subroutine name used to key static
// function-local variables (§13.4.2), and the simulation/evaluation context.
// This quartet travels together through the entire recursive statement
// executor, so it is bundled into one entity rather than passed field by
// field.
struct FuncExecCtx {
  Variable* ret_var;
  std::string_view func_name;
  SimContext& ctx;
  Arena& arena;
  // The declared width of the return value, or zero where the return type has
  // no packed width -- void, a string, a class handle, a parameterized method's
  // type. ExecFuncReturn reads zero as "leave the expression's own vector
  // alone".
  uint32_t ret_width;
};

static bool ExecFuncStmt(const Stmt* stmt, const FuncExecCtx& exec);
static bool ExecFuncBlock(const Stmt* stmt, const FuncExecCtx& exec);

// Returns the trailing unconditional else of an if/else-if chain, or null when
// the chain has no final else.
static const Stmt* FuncFindFinalElse(const Stmt* stmt) {
  const Stmt* cur = stmt;
  while (cur->else_branch && cur->else_branch->kind == StmtKind::kIf) {
    cur = cur->else_branch;
  }
  return cur->else_branch;
}

// Aggregated result of evaluating the conditions of a unique-if chain.
struct UniqueIfScan {
  int match_count = 0;
  const Stmt* first_match = nullptr;
  bool has_final_else = false;
};

// Evaluates every condition in the if/else-if chain in source order, recording
// how many matched, the first match, and whether the chain ends in a final
// else.
static UniqueIfScan ScanUniqueIfChain(const Stmt* stmt, SimContext& ctx,
                                      Arena& arena) {
  UniqueIfScan scan;
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    if (EvalExpr(cur->condition, ctx, arena).IsTruthy()) {
      scan.match_count++;
      if (!scan.first_match) scan.first_match = cur;
    }
    if (cur->else_branch && cur->else_branch->kind != StmtKind::kIf) {
      scan.has_final_else = true;
    }
  }
  return scan;
}

// Runs the branch selected by a unique-if scan: the first matching arm, else
// the trailing unconditional else, reporting a no-match violation for a plain
// `unique` chain that has no final else.
static bool ExecFuncUniqueIfBranch(const Stmt* stmt, const UniqueIfScan& scan,
                                   CaseQualifier qual,
                                   const FuncExecCtx& exec) {
  if (scan.first_match) {
    return ExecFuncStmt(scan.first_match->then_branch, exec);
  }
  if (scan.has_final_else) {
    const Stmt* final_else = FuncFindFinalElse(stmt);
    if (final_else) return ExecFuncStmt(final_else, exec);
  } else if (qual == CaseQualifier::kUnique) {
    exec.ctx.AddPendingViolation(stmt->range.start,
                                 "unique if: no condition matched",
                                 Subclause("12.4.2.1"));
  }
  return false;
}

// A unique/unique0/priority if encountered while running a function or task
// body performs the same violation checks as one in a process body (§12.4.2).
// Because the report queue is keyed on the calling process (§12.4.2.2), routing
// the report through AddPendingViolation attributes it to whichever process
// invoked the subroutine; separate callers therefore accumulate and flush
// independently.
static bool ExecFuncUniqueIf(const Stmt* stmt, CaseQualifier qual,
                             const FuncExecCtx& exec) {
  UniqueIfScan scan = ScanUniqueIfChain(stmt, exec.ctx, exec.arena);
  if (scan.match_count > 1) {
    exec.ctx.AddPendingViolation(stmt->range.start,
                                 "unique if: multiple conditions matched",
                                 Subclause("12.4.2.1"));
  }
  return ExecFuncUniqueIfBranch(stmt, scan, qual, exec);
}

static bool ExecFuncPriorityIf(const Stmt* stmt, const FuncExecCtx& exec) {
  bool has_final_else = false;
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    if (EvalExpr(cur->condition, exec.ctx, exec.arena).IsTruthy()) {
      return ExecFuncStmt(cur->then_branch, exec);
    }
    if (cur->else_branch && cur->else_branch->kind != StmtKind::kIf) {
      has_final_else = true;
    }
  }
  if (has_final_else) {
    const Stmt* final_else = FuncFindFinalElse(stmt);
    if (final_else) return ExecFuncStmt(final_else, exec);
  } else {
    exec.ctx.AddPendingViolation(stmt->range.start,
                                 "priority if: no condition matched",
                                 Subclause("12.4.2.1"));
  }
  return false;
}

static bool ExecFuncIf(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);

  auto qual = stmt->qualifier;
  bool r = false;
  if (qual == CaseQualifier::kUnique || qual == CaseQualifier::kUnique0) {
    r = ExecFuncUniqueIf(stmt, qual, exec);
  } else if (qual == CaseQualifier::kPriority) {
    r = ExecFuncPriorityIf(stmt, exec);
  } else {
    auto cond = EvalExpr(stmt->condition, exec.ctx, exec.arena);
    if (cond.ToUint64() != 0) {
      r = ExecFuncStmt(stmt->then_branch, exec);
    } else if (stmt->else_branch) {
      r = ExecFuncStmt(stmt->else_branch, exec);
    } else {
      r = false;
    }
  }

  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return r;
}

static bool ExecFuncBlock(const Stmt* stmt, const FuncExecCtx& exec) {
  bool named = !stmt->label.empty();
  if (named) exec.ctx.PushStaticScope(stmt->label);
  for (auto* c : stmt->stmts) {
    if (ExecFuncStmt(c, exec)) {
      if (named) exec.ctx.PopStaticScope(stmt->label);
      return true;
    }
  }
  if (named) exec.ctx.PopStaticScope(stmt->label);
  return false;
}

// True when any for-loop init declares a new variable (has an explicit type),
// which requires a fresh scope to hold the loop-local declarations.
static bool ForInitNeedsScope(const Stmt* stmt) {
  for (const auto& t : stmt->for_init_types) {
    if (t.kind != DataTypeKind::kImplicit) return true;
  }
  return false;
}

// Runs the for-loop initializers: typed inits create loop-local variables,
// while untyped inits execute as ordinary statements.
static void ExecFuncForInits(const Stmt* stmt, const FuncExecCtx& exec) {
  for (size_t i = 0; i < stmt->for_inits.size(); ++i) {
    auto* init = stmt->for_inits[i];
    if (i < stmt->for_init_types.size() &&
        stmt->for_init_types[i].kind != DataTypeKind::kImplicit && init &&
        init->lhs && init->lhs->kind == ExprKind::kIdentifier) {
      uint32_t w = EvalTypeWidth(stmt->for_init_types[i]);
      if (w == 0) w = 32;
      // §6.11.3: byte, shortint, int, integer and longint default to signed,
      // so the declared type decides the loop variable's signedness as it
      // decides any other local's. Created from the width alone, an int
      // counter compared its negative values as huge positive ones.
      auto* v = exec.ctx.CreateLocalVariable(
          init->lhs->text, w, IsSignedType(stmt->for_init_types[i], {}));
      if (init->rhs) v->value = EvalExpr(init->rhs, exec.ctx, exec.arena);
    } else if (init) {
      ExecFuncStmt(init, exec);
    }
  }
}

// Runs the condition/body/step iterations of a for-loop. Returns true when the
// body executed a return (so the caller should propagate it).
static bool ExecFuncForLoop(const Stmt* stmt, const FuncExecCtx& exec) {
  while (stmt->for_cond &&
         EvalExpr(stmt->for_cond, exec.ctx, exec.arena).IsTruthy()) {
    if (stmt->for_body && ExecFuncStmt(stmt->for_body, exec)) {
      return true;
    }
    for (auto* step : stmt->for_steps) ExecFuncStmt(step, exec);
  }
  return false;
}

static bool ExecFuncFor(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);
  bool scoped = ForInitNeedsScope(stmt);
  if (scoped) exec.ctx.PushScope();
  ExecFuncForInits(stmt, exec);
  bool returned = ExecFuncForLoop(stmt, exec);
  if (scoped) exec.ctx.PopScope();
  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return returned;
}

bool DeclaredTypeIs4State(const DataType& type) {
  if (type.kind == DataTypeKind::kNamed) return true;
  return Is4stateType(type.kind);
}

static Variable* CreateFuncLocalVar(std::string_view name, const DataType& type,
                                    const Expr* init, SimContext& ctx,
                                    Arena& arena) {
  // A class-typed local (user class, or the built-in `process`/handle types)
  // holds a 64-bit handle and must record its class type so later method calls
  // such as `p.suspend()` dispatch -- module-scope decls do this via
  // TryExecClassVarDecl, but function-body locals take this path instead.
  bool is_class = !type.type_name.empty() && ctx.FindClassType(type.type_name);
  // §6.18: a local declared with a user-defined type name is an object of the
  // type that name stands for, so `nib v` is as wide as `nib` is.
  // DeclaredTypeWidth is what reaches that width; the one-argument
  // EvalTypeWidth gives a DataTypeKind::kNamed no width at all, and the
  // fallback below then made every typedef'd body local 32 bits. This is the
  // site a subroutine body's declaration takes -- the statement executor's own
  // ExecVarDeclImpl serves a declaration outside a subroutine -- so the two
  // have to reach the typedef table separately.
  uint32_t declared = is_class ? 64 : DeclaredTypeWidth(type, ctx);
  // §6.16: a string has no declared width and starts as "", so it is created
  // with none rather than at the carrier width below, and marked so that what
  // reads a string reads the flag rather than a width. A declaration outside a
  // subroutine does both in CreateDeclVariable; without them here,
  // ExecFuncIdentifierAssign would take the length of whatever the local was
  // last assigned for a declared width and truncate to it. The flag is set on
  // the variable this call created rather than through
  // SimContext::RegisterStringVariable, which resolves a name and would reach a
  // variable of the design that the local shadows.
  bool is_string = !is_class && type.kind == DataTypeKind::kString;
  uint32_t w = declared ? declared : (is_string ? 0 : 32);
  // §6.11.3: a body local carries its declared signedness exactly as a
  // module-scope declaration does (Lowerer sets the same flag there), so an
  // `integer` local is a signed operand rather than an unsigned one.
  auto* v = ctx.CreateLocalVariable(name, w, IsSignedType(type, {}));
  v->is_4state = DeclaredTypeIs4State(type);
  if (is_string) v->is_string = true;
  if (is_class) ctx.SetVariableClassType(name, type.type_name);
  RecordVariableEnumType(name, type, ctx);
  if (init == nullptr) return v;
  // §8.4: `P p = new;` creates an object of class P and assigns its handle to
  // p. `new` names a construction, not a value to be read, so evaluating it as
  // an ordinary initializer expression yields no object and leaves the handle
  // null. A class-typed local with a `new` initializer is therefore constructed
  // here, as the declaration path for a variable outside a subroutine does.
  if (is_class && init->kind == ExprKind::kCall && init->text == "new") {
    v->value =
        EvalClassNew(type.type_name, init, ctx, arena, init->range.start);
    ApplyClassParamOverrides(name, v->value.ToUint64(), ctx, arena);
    return v;
  }
  // §6.8 states a variable declaration assignment as an assignment to the
  // declared variable, so §10.7 truncates or extends the initializer into the
  // width the type declares rather than letting it put its own vector in place:
  // a Logic4Vec carries its own width, and a sized literal is self-determined,
  // so `nib v = 8'hFF` left v eight bits holding 255.
  //
  // The target is the declared width and not the width the variable was created
  // at, because the 32 above is a carrier for a type nothing here could size
  // rather than a width the source asked for. A string local (§6.16) is the
  // case that turns on the difference: it is created at that carrier width and
  // has no declared width at all, and its initializer is what gives it one.
  // ResizeToWidth leaves a value alone at a target of 0, so such a local keeps
  // the behaviour it had.
  v->value = ResizeToWidth(EvalExpr(init, ctx, arena), declared, arena);
  return v;
}

static void ExecFuncVarDeclAutomatic(const Stmt* stmt,
                                     const FuncExecCtx& exec) {
  CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type, stmt->var_init,
                     exec.ctx, exec.arena);
}

static void ExecFuncVarDeclStatic(const Stmt* stmt, const FuncExecCtx& exec) {
  auto* existing = exec.ctx.FindStaticFuncVar(exec.func_name, stmt->var_name);
  if (existing) {
    exec.ctx.AliasLocalVariable(stmt->var_name, existing);
    return;
  }
  auto* v = CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type,
                               stmt->var_init, exec.ctx, exec.arena);
  exec.ctx.SaveStaticFuncVar(exec.func_name, stmt->var_name, v);
}

static void ExecFuncVarDecl(const Stmt* stmt, const FuncExecCtx& exec) {
  if (stmt->var_is_automatic) {
    ExecFuncVarDeclAutomatic(stmt, exec);
    return;
  }
  if (stmt->var_is_static) {
    ExecFuncVarDeclStatic(stmt, exec);
    return;
  }
  if (exec.ctx.FindLocalVariable(stmt->var_name)) return;
  CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type, stmt->var_init,
                     exec.ctx, exec.arena);
}

static std::string GetForeachArrayName(const Expr* expr) {
  if (!expr) return {};
  if (expr->kind == ExprKind::kIdentifier) return std::string(expr->text);
  if (expr->kind == ExprKind::kMemberAccess) {
    std::string name;
    BuildLhsName(expr, name);
    return name;
  }
  return {};
}

static bool ExecFuncWhile(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);
  while (stmt->condition &&
         EvalExpr(stmt->condition, exec.ctx, exec.arena).IsTruthy()) {
    if (stmt->body && ExecFuncStmt(stmt->body, exec)) {
      if (labeled) exec.ctx.PopStaticScope(stmt->label);
      return true;
    }
  }
  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return false;
}

static bool ExecFuncDoWhile(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);
  do {
    if (stmt->body && ExecFuncStmt(stmt->body, exec)) {
      if (labeled) exec.ctx.PopStaticScope(stmt->label);
      return true;
    }
  } while (stmt->condition &&
           EvalExpr(stmt->condition, exec.ctx, exec.arena).IsTruthy());
  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return false;
}

static bool ExecFuncForever(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);
  for (;;) {
    if (stmt->body && ExecFuncStmt(stmt->body, exec)) {
      if (labeled) exec.ctx.PopStaticScope(stmt->label);
      return true;
    }
  }
  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return false;
}

// Resolves the iteration count for a foreach over the named array: the array's
// element count when known, otherwise the bit width of a matching variable.
static uint32_t ResolveForeachSize(std::string_view name, SimContext& ctx) {
  auto* info = ctx.FindArrayInfo(name);
  if (info) return info->size;
  auto* var = ctx.FindVariable(name);
  return var ? var->value.width : 0;
}

// Runs the iteration loop of a foreach over an array of `size` elements,
// pushing a scope that holds the (optional) loop index variable. Returns true
// when the body executed a return.
static bool ExecFuncForeachLoop(const Stmt* stmt, uint32_t size,
                                const FuncExecCtx& exec) {
  std::string_view iter_name;
  if (!stmt->foreach_vars.empty() && !stmt->foreach_vars[0].empty()) {
    iter_name = stmt->foreach_vars[0];
  }

  exec.ctx.PushScope();
  Variable* iter_var = nullptr;
  if (!iter_name.empty()) {
    iter_var = exec.ctx.CreateLocalVariable(iter_name, 32);
  }

  for (uint32_t i = 0; i < size; ++i) {
    if (iter_var) {
      iter_var->value = MakeLogic4VecVal(exec.arena, 32, i);
    }
    if (stmt->body && ExecFuncStmt(stmt->body, exec)) {
      exec.ctx.PopScope();
      return true;
    }
  }

  exec.ctx.PopScope();
  return false;
}

static bool ExecFuncForeach(const Stmt* stmt, const FuncExecCtx& exec) {
  bool labeled = !stmt->label.empty();
  if (labeled) exec.ctx.PushStaticScope(stmt->label);
  std::string name = GetForeachArrayName(stmt->expr);
  uint32_t size = name.empty() ? 0 : ResolveForeachSize(name, exec.ctx);
  bool returned = false;
  if (size != 0) {
    returned = ExecFuncForeachLoop(stmt, size, exec);
  }
  if (labeled) exec.ctx.PopStaticScope(stmt->label);
  return returned;
}

// Carries out a `return <expr>;`. §13.4.1: the function definition implicitly
// declares a variable internal to the function, and "this variable has the same
// type as the function return value", so a return is an assignment to a typed
// object rather than a replacement of it. §10.7 then decides the value: the
// expression is extended or truncated to the declared width, extending by the
// expression's own signedness, and the object keeps the signedness its
// declaration gave it. The other form §13.4.1 offers -- assigning to the
// function's name -- goes through the ordinary assignment executor and has
// always done this; a `return` that took the expression's vector whole handed
// the caller a `logic [7:0]` function's result 32 bits wide, and let a 1-bit
// comparison's signedness stand in for an `int`'s.
static void ExecFuncReturn(const Stmt* stmt, const FuncExecCtx& exec) {
  Logic4Vec val =
      EvalExpr(stmt->expr, exec.ctx, exec.arena, exec.ret_var->value.width);
  if (exec.ret_width != 0) {
    val = ResizeToWidth(val, exec.ret_width, exec.arena);
    val.is_signed = exec.ret_var->is_signed;
  }
  exec.ret_var->value = val;
  // §6.11.2: §13.4.1 gives the implicit variable the function's return type, so
  // a `return` into a 2-state one converts its unknowns to zeros. The
  // assignment form `f = expr;` is converted by ExecFuncIdentifierAssign, which
  // this statement does not go through.
  if (!exec.ret_var->is_4state) CoerceTo2State(exec.ret_var->value);
}

static bool ExecFuncStmt(const Stmt* stmt, const FuncExecCtx& exec) {
  if (!stmt) return false;
  switch (stmt->kind) {
    case StmtKind::kReturn:
      if (stmt->expr) ExecFuncReturn(stmt, exec);
      return true;
    case StmtKind::kBlockingAssign:
      ExecFuncBlockingAssign(stmt, exec.ctx, exec.arena);
      return false;
    case StmtKind::kNonblockingAssign:
      // §13.4.4: a nonblocking assignment is legal in a function body; it
      // schedules into the NBA region just as it does in a process, rather
      // than being dropped. The enclosing call runs inside a process, so the
      // scheduler is active to drain the update.
      ExecNonblockingAssignImpl(stmt, exec.ctx, exec.arena);
      return false;
    case StmtKind::kExprStmt:
      if (!TryExecSystemCallTask(stmt->expr, exec.ctx, exec.arena)) {
        EvalExpr(stmt->expr, exec.ctx, exec.arena);
      }
      return false;
    case StmtKind::kVarDecl:
      ExecFuncVarDecl(stmt, exec);
      return false;
    case StmtKind::kIf:
      return ExecFuncIf(stmt, exec);
    case StmtKind::kBlock:
      return ExecFuncBlock(stmt, exec);
    case StmtKind::kFor:
      return ExecFuncFor(stmt, exec);
    case StmtKind::kForeach:
      return ExecFuncForeach(stmt, exec);
    case StmtKind::kWhile:
      return ExecFuncWhile(stmt, exec);
    case StmtKind::kDoWhile:
      return ExecFuncDoWhile(stmt, exec);
    case StmtKind::kForever:
      return ExecFuncForever(stmt, exec);
    case StmtKind::kFork:
      // §13.4.4: a function may fork off background processes with join_none
      // (join/join_any would block and are illegal here). Spawn the children
      // and continue; the function itself does not wait.
      SpawnForkJoinNone(stmt, exec.ctx, exec.arena);
      return false;
    case StmtKind::kAssertImmediate:
    case StmtKind::kAssumeImmediate:
    case StmtKind::kCoverImmediate:
      // §16.4.5: a deferred immediate assertion inside a function is evaluated
      // and its report scheduled against the calling process, so each process
      // that calls the function reports independently. A simple immediate
      // assertion in a function is outside this subclause and left unhandled.
      if (stmt->is_deferred)
        ExecDeferredImmediateAssertInFunction(stmt, exec.ctx, exec.arena);
      return false;
    default:
      return false;
  }
}

void ExecFunctionBody(const ModuleItem* func, Variable* ret_var,
                      SimContext& ctx, Arena& arena) {
  // A return type nothing can size -- void, a string, a class handle, a
  // parameterized method's type -- leaves the return statement to take the
  // expression's own vector, which is what it has always done. A typedef name
  // is sized, through the type_widths table, so §13.4.1's implicit variable
  // holds the width the name declares rather than the returned expression's.
  uint32_t ret_width =
      DeclaredTypeWidth(func->return_type, ctx) == 0 ? 0 : ret_var->value.width;
  FuncExecCtx exec{ret_var, func->name, ctx, arena, ret_width};
  for (auto* s : func->func_body_stmts) {
    if (ExecFuncStmt(s, exec)) return;
  }
}

}  // namespace delta
