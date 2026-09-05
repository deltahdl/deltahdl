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
#include "simulator/stmt_exec.h"

namespace delta {
// The statement executor for a subroutine body (13.4). A function or task
// body does not run on the scheduler the way a procedural block does: it runs
// to completion within the caller's evaluation, so it needs its own execution
// of every statement form -- assignments, declarations, conditionals and
// loops -- that returns as soon as a `return` is reached. Those live here;
// eval_function_args.cpp holds the argument binding and write-back that
// surround a call.

static void ExecFuncSelectAssign(const Expr* lhs, const Logic4Vec& val,
                                 SimContext& ctx, Arena& arena) {
  // §7.8.1 and §7.8.4 decide what key an index yields: a wildcard index is
  // self-determined and unsigned, and a typed integral index is cast to the
  // declared index width, sign-extended when the index type is signed and
  // zero-extended when it is not. §7.8.6 rules that a write through an index
  // holding an x or z bit performs no operation and issues a warning.
  // TryAssocIndexedWrite applies all three, so calling it here leaves one
  // function deciding the key an associative array write uses: `aa[-1] = v`
  // reaches the entry in a subroutine body that the same statement reaches
  // among a module's items, rather than a second entry of its own. It declines
  // (returning false) when the base is not an identifier naming an associative
  // array, leaving the fixed-size array element write below.
  if (TryAssocIndexedWrite(lhs, val, ctx, arena)) return;
  if (!lhs->base || lhs->base->kind != ExprKind::kIdentifier) return;
  auto idx = EvalExpr(lhs->index, ctx, arena).ToUint64();
  auto name = std::string(lhs->base->text) + "[" + std::to_string(idx) + "]";
  auto* elem = ctx.FindVariable(name);
  if (elem) elem->value = val;
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
static void WriteSelfProperty(ClassObject* self, std::string_view name,
                              const Logic4Vec& val, SimContext& ctx) {
  // §8.11: a `this.x` write updates the invoking instance. Properties are kept
  // under both an unscoped key and a `Type::name` scoped key, and reads consult
  // the scoped key first. In a plain instance method (no enclosing-class
  // context, unlike a constructor) fall back to the object's own type so both
  // copies stay in sync; otherwise the write lands only on the unscoped key and
  // the next read returns the stale scoped value.
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  if (!enclosing) enclosing = self->type;
  if (enclosing) {
    self->SetPropertyForType(name, enclosing, val);
  } else {
    self->SetProperty(std::string(name), val);
  }
}

// Assigns to a plain identifier lhs: writes the local variable when present,
// otherwise falls back to a property on the current `this` object.
static void ExecFuncIdentifierAssign(const Expr* lhs, const Logic4Vec& val,
                                     SimContext& ctx) {
  auto* var = ctx.FindVariable(lhs->text);
  if (var) {
    var->value = val;
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
  if (self) WriteSelfProperty(self, lhs->text, val, ctx);
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
      ctx);
  return true;
}

// Run the blocking-assignment handlers that do not need the generic
// right-hand-side value: the three `new` forms and a queue target. Returns
// true when one of them fully handled the assignment.
static bool TryFuncSpecialBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                         Arena& arena) {
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
  if (lhs->kind == ExprKind::kIdentifier) {
    ExecFuncIdentifierAssign(lhs, val, ctx);
    return;
  }
  if (lhs->kind == ExprKind::kSelect) {
    ExecFuncSelectAssign(lhs, val, ctx, arena);
    return;
  }
  if (IsMemberAccessOn(lhs, "this")) {
    auto* self = ctx.CurrentThis();
    if (self) WriteSelfProperty(self, lhs->rhs->text, val, ctx);
    return;
  }
  if (IsMemberAccessOn(lhs, "super")) {
    auto* self = ctx.CurrentThis();
    if (self && self->type && self->type->parent) {
      self->SetPropertyForType(std::string(lhs->rhs->text), self->type->parent,
                               val);
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

static void ExecFuncBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  if (!stmt->lhs) return;
  if (TryFuncSpecialBlockingAssign(stmt, ctx, arena)) return;
  ExecFuncWriteValue(stmt->lhs, EvalExpr(stmt->rhs, ctx, arena), ctx, arena);
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
      auto* v = exec.ctx.CreateLocalVariable(init->lhs->text, w);
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

static Variable* CreateFuncLocalVar(std::string_view name, const DataType& type,
                                    const Expr* init, SimContext& ctx,
                                    Arena& arena) {
  // A class-typed local (user class, or the built-in `process`/handle types)
  // holds a 64-bit handle and must record its class type so later method calls
  // such as `p.suspend()` dispatch -- module-scope decls do this via
  // TryExecClassVarDecl, but function-body locals take this path instead.
  bool is_class = !type.type_name.empty() && ctx.FindClassType(type.type_name);
  uint32_t w = is_class ? 64 : EvalTypeWidth(type);
  if (w == 0) w = 32;
  // §6.11.3: a body local carries its declared signedness exactly as a
  // module-scope declaration does (Lowerer sets the same flag there), so an
  // `integer` local is a signed operand rather than an unsigned one.
  auto* v = ctx.CreateLocalVariable(name, w, IsSignedType(type, {}));
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
  v->value = EvalExpr(init, ctx, arena);
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
  // A return type EvalTypeWidth cannot size -- void, a string, a class handle,
  // a parameterized method's type -- leaves the return statement to take the
  // expression's own vector, which is what it has always done.
  uint32_t ret_width =
      EvalTypeWidth(func->return_type) == 0 ? 0 : ret_var->value.width;
  FuncExecCtx exec{ret_var, func->name, ctx, arena, ret_width};
  for (auto* s : func->func_body_stmts) {
    if (ExecFuncStmt(s, exec)) return;
  }
}

}  // namespace delta
