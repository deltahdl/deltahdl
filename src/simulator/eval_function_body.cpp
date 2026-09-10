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
#include "simulator/vpi_design_attach.h"

namespace delta {
// The statement executor for a subroutine body (13.4). A function or task
// body does not run on the scheduler the way a procedural block does: it runs
// to completion within the caller's evaluation, so it needs its own execution
// of every statement form -- declarations, conditionals and loops -- that
// returns as soon as a `return` is reached. Those live here;
// eval_function_body_assign.cpp holds the assignment forms the same executor
// dispatches to, and eval_function_args.cpp the argument binding and
// write-back that surround a call.

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
          init->lhs->text, w,
          DeclaredTypeIsSigned(stmt->for_init_types[i], exec.ctx));
      // §6.11.2: the declared type decides whether the loop variable can hold
      // an unknown at all -- "when a 4-state value is automatically converted
      // to a 2-state value, any unknown or high-impedance bits shall be
      // converted to zeros" -- and the flag defaults to true, so an `int`
      // counter kept the x and z its initializer read. CreateFuncLocalVar sets
      // the same flag for an ordinary body local from the same answer.
      v->is_4state = DeclaredTypeIs4State(stmt->for_init_types[i]);
      // §10.7 sizes the right-hand side to the left-hand side, and the width
      // the type declares reached the cell CreateLocalVariable made and was
      // then thrown away by the store: a Logic4Vec carries its own width, so
      // `for (int i = seed; ...)` over a `logic [7:0] seed` left i eight bits
      // wide for every later read, step and comparison. The initializer is
      // copied for the reason CreateFuncLocalVar copies its own (§6.8): `for
      // (int i = n; ...)` would otherwise leave i and n one storage element,
      // and the loop's own step is the store that shows it. The copy goes
      // outside the resize because ResizeToWidth answers its argument
      // untouched when the widths already match, which is precisely the
      // aliased case, and the coercion below writes in place -- through a
      // shared buffer it would clear the source variable's own unknown bits.
      if (init->rhs) {
        v->value =
            OwnRhsWords(ResizeToWidth(EvalExpr(init->rhs, exec.ctx, exec.arena),
                                      w, exec.arena),
                        exec.arena);
        if (!v->is_4state) CoerceTo2State(v->value);
      }
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
  bool is_string = !is_class && DeclaredTypeIsString(type, ctx);
  uint32_t w = declared ? declared : (is_string ? 0 : 32);
  // §6.11.3: a body local carries its declared signedness exactly as a
  // module-scope declaration does (Lowerer sets the same flag there), so an
  // `integer` local is a signed operand rather than an unsigned one.
  auto* v = ctx.CreateLocalVariable(name, w, DeclaredTypeIsSigned(type, ctx));
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
  //
  // §6.8 also calls a variable "an abstraction of a data storage element"
  // that "shall store a value from one assignment to the next". An initializer
  // that reads another variable is answered with that variable's own Logic4Vec,
  // and a Logic4Vec copies its words pointer, so `bit [7:0] y = x;` left y and
  // x one element. The declaration is quiet about it -- nothing writes in place
  // here -- and the next store to y is what shows it: ExecFuncIdentifierAssign
  // coerces a 2-state target in place and cleared x's x/z bits through the
  // shared words. The copy goes outside the resize rather than inside because
  // ResizeToWidth returns its argument untouched when the widths already match,
  // which is precisely the aliased case; outside, it covers every path, and is
  // merely redundant on the path where the resize itself allocated.
  v->value = OwnRhsWords(
      ResizeToWidth(EvalExpr(init, ctx, arena), declared, arena), arena);
  // §6.11.2: "when a 4-state value is automatically converted to a 2-state
  // value, any unknown or high-impedance bits shall be converted to zeros", and
  // §6.8 makes a variable declaration assignment an assignment to the declared
  // variable, so a 2-state local declared from a 4-state initializer holds
  // zeros where that initializer held x or z. The flag was recorded above and
  // applied by nothing on this path: every later store consults it in
  // ExecFuncIdentifierAssign, so `int v; v = seed;` converted where `int v =
  // seed;` did not -- two spellings of one declaration with two answers. The
  // coercion writes in place and so goes after the copy, never through the
  // value the initializer produced: an initializer that reads another variable
  // is answered with that variable's own Logic4Vec, and coercing through it
  // would clear the source's own unknown bits (#3563).
  if (!v->is_4state) CoerceTo2State(v->value);
  return v;
}

// §7.10/§7.4.2: the storage the declaration's own dimensions ask for, which a
// body local needs as much as a declaration outside a subroutine does. The
// variable CreateFuncLocalVar makes carries one element's width, and
// CreateDeclAggregate makes the queue or the elements beside it, which is the
// step the two paths did not share: `int q[$];` in a task body was a plain
// vector, and since the elaborator now gives a procedural declaration the
// dimensions its typedef carries, `q_t qu;` reaches here with the same
// dimensions and the same need.
static void CreateFuncLocalAggregate(const Stmt* stmt, Variable* var,
                                     const FuncExecCtx& exec) {
  if (var == nullptr) return;
  CreateDeclAggregate(stmt, var->value.width, exec.ctx, exec.arena);
}

static void ExecFuncVarDeclAutomatic(const Stmt* stmt,
                                     const FuncExecCtx& exec) {
  auto* v = CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type,
                               stmt->var_init, exec.ctx, exec.arena);
  CreateFuncLocalAggregate(stmt, v, exec);
}

static void ExecFuncVarDeclStatic(const Stmt* stmt, const FuncExecCtx& exec) {
  auto* existing = exec.ctx.FindStaticFuncVar(exec.func_name, stmt->var_name);
  if (existing) {
    exec.ctx.AliasLocalVariable(stmt->var_name, existing);
    return;
  }
  auto* v = CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type,
                               stmt->var_init, exec.ctx, exec.arena);
  CreateFuncLocalAggregate(stmt, v, exec);
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
  auto* v = CreateFuncLocalVar(stmt->var_name, stmt->var_decl_type,
                               stmt->var_init, exec.ctx, exec.arena);
  CreateFuncLocalAggregate(stmt, v, exec);
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
  // §6.8, printed page 105: a variable "shall store a value from one assignment
  // to the next", so the implicit return variable and the returned one are two
  // storage elements and neither may hold the other's words. EvalExpr answers a
  // bare identifier's, an unpacked element's or a class property's own vector,
  // and ResizeToWidth passes a value already at the declared width straight
  // through, so the CoerceTo2State below would write into whatever was
  // returned -- and a returned `ref` or `output` formal carries that back out
  // to the caller's argument.
  Logic4Vec val = OwnRhsWords(
      EvalExpr(stmt->expr, exec.ctx, exec.arena, exec.ret_var->value.width),
      exec.arena);
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
  // §37.44 detail 1: "as a thread works its way down a call chain of tasks
  // and/or functions, a new frame is activated as each new task or function is
  // entered". This is that entry for a function or a method, and the scope is
  // what leaves the frame that was active standing again however the body ends
  // -- a return out of the middle of it included.
  VpiActiveFrameScope frame;
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
