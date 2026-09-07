#include <algorithm>
#include <cmath>
#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaborator/queue_dim.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

// §7.8 writes an associative array's dimension as the type its index has, and
// §7.8.1 writes the wildcard index as `*`. The parser records both as an
// identifier naming the type, which is the shape §7.4.2's size form also has
// when the size is a parameter, so the two are told apart by what the name
// means rather than by how the dimension is written: an index type is a
// keyword, the wildcard, a class, or a name the elaborated typedef table
// answers for, and a size is anything else.
//
// A name the table answers 0 for is read as a size. That is the string typedef
// of #3486, which the table cannot distinguish from a type it never saw; an
// associative array keyed by one builds nothing either way, since evaluating a
// type name as an expression yields no size, so the reading costs nothing that
// was working.
static bool IsAssocIndexDim(const Expr* dim, SimContext& ctx) {
  if (!dim || dim->kind != ExprKind::kIdentifier) return false;
  if (dim->text == "*") return true;
  if (TypeNameToDataType(dim->text).kind != DataTypeKind::kNamed) return true;
  if (ctx.FindClassType(dim->text) != nullptr) return true;
  return ctx.FindTypeWidth(dim->text) != 0;
}

// §7.4.2: "A fixed-size unpacked dimension may also be specified by a single
// positive constant integer expression to specify the number of elements in the
// unpacked dimension, as in C. In this case, [size] shall mean the same as
// [0:size-1]." The clause's own example gives `int Array[8][32]` and
// `int Array[0:7][0:31]` as the same declaration, so the size form is the
// ascending range counting from zero and is returned here as that range's upper
// bound.
//
// Only a lone dimension is read this way. The range form below takes the first
// of several and builds one dimension from it, which #3488 is; giving the size
// form the same treatment would spread that reading rather than answer it.
//
// A queue dimension does not reach here: CreateBlockQueue is asked first and
// answers for every `[$]` and `[$:N]`.
static std::optional<int64_t> BlockArraySizeFormUpperBound(const Stmt* stmt,
                                                           const Expr* dim,
                                                           SimContext& ctx,
                                                           Arena& arena) {
  if (stmt->var_unpacked_dims.size() != 1) return std::nullopt;
  if (IsAssocIndexDim(dim, ctx)) return std::nullopt;
  auto size = static_cast<int64_t>(EvalExpr(dim, ctx, arena).ToUint64());
  // §7.4.2 asks for a positive size. A declaration that gives anything else is
  // reported by the elaborator's ApplyConstSizedUnpackedDim, so nothing is
  // built here and the same rule is not named twice.
  if (size <= 0) return std::nullopt;
  return size - 1;
}

static void CreateBlockArrayElements(const Stmt* stmt, uint32_t elem_width,
                                     SimContext& ctx, Arena& arena) {
  if (stmt->var_unpacked_dims.empty()) return;
  auto* dim = stmt->var_unpacked_dims[0];
  if (!dim) return;
  int64_t left = 0;
  int64_t right = 0;
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    left = static_cast<int64_t>(EvalExpr(dim->lhs, ctx, arena).ToUint64());
    right = static_cast<int64_t>(EvalExpr(dim->rhs, ctx, arena).ToUint64());
  } else if (auto hi = BlockArraySizeFormUpperBound(stmt, dim, ctx, arena)) {
    right = *hi;
  } else {
    return;
  }
  auto lo = static_cast<uint32_t>(std::min(left, right));
  auto size = static_cast<uint32_t>(std::abs(left - right) + 1);
  ArrayInfo info;
  info.lo = lo;
  info.size = size;
  info.elem_width = elem_width;
  info.is_descending = (left > right);
  // §23.9: a declaration inside a begin-end block is local to that block, so
  // its shape goes away with the block rather than answering for a like-named
  // variable after it. The element variables below are created the same way a
  // few lines down in this file.
  ctx.RegisterArrayInScope(stmt->var_name, info);
  for (uint32_t i = 0; i < size; ++i) {
    uint32_t idx = lo + i;
    auto name = std::string(stmt->var_name) + "[" + std::to_string(idx) + "]";
    ctx.CreateVariable(*arena.Create<std::string>(std::move(name)), elem_width);
  }
}

// §7.10: a declaration whose first unpacked dimension is `[$]` or `[$:N]`
// declares a queue, wherever the declaration stands. Creates the QueueObject
// the queue methods of §7.10.2 operate on, so that a declaration inside a
// procedural block gets the same backing store a declaration among a module's
// items gets from Lowerer::LowerVarAggregate. Returns true when it made one.
static bool CreateBlockQueue(const Stmt* stmt, uint32_t elem_width,
                             SimContext& ctx, Arena& arena) {
  if (stmt->var_unpacked_dims.empty()) return false;
  const auto* dim = stmt->var_unpacked_dims[0];
  if (!IsQueueDim(dim)) return false;
  // §7.10.5: N in `[$:N]` bounds the queue at N + 1 elements, and `[$]` leaves
  // it unbounded, which CreateQueue spells -1. A bound the subclause rules out
  // is left unbounded here rather than reported: the elaborator's
  // CheckBlockQueueBounds already reports it, and a second report of one
  // declaration's one error would name the same rule twice.
  int32_t max_size = -1;
  if (dim->rhs) {
    auto bound =
        static_cast<int64_t>(EvalExpr(dim->rhs, ctx, arena).ToUint64());
    if (auto size = QueueBoundMaxSize(bound)) max_size = *size;
  }
  ctx.CreateQueue(stmt->var_name, elem_width, max_size,
                  Is4stateType(stmt->var_decl_type.kind));
  return true;
}

static bool TryExecWeakRefVarDecl(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  if (stmt->var_decl_type.type_name != "weak_reference") return false;
  ctx.CreateVariable(stmt->var_name, 64);
  ctx.SetVariableClassType(stmt->var_name, "weak_reference");
  const auto& type_params = stmt->var_decl_type.type_params;
  if (!type_params.empty()) {
    std::vector<Expr*> exprs;
    exprs.reserve(type_params.size());
    for (const auto& tp : type_params) {
      exprs.push_back(tp.type_ref_expr);
    }
    ctx.SetVariableClassParamExprs(stmt->var_name, std::move(exprs));
  }
  if (!stmt->var_init || stmt->var_init->kind != ExprKind::kCall ||
      stmt->var_init->text != "new")
    return true;
  uint64_t referent = kNullClassHandle;
  if (!stmt->var_init->args.empty()) {
    auto val = EvalExpr(stmt->var_init->args[0], ctx, arena);
    referent = val.ToUint64();
  }
  auto wr_handle = ctx.AllocateWeakReference(referent, arena);
  auto* var = ctx.FindVariable(stmt->var_name);
  if (var) var->value = MakeLogic4VecVal(arena, 64, wr_handle);
  return true;
}

// Records the class type-parameter override expressions (if any) for the
// just-created class variable `var_name`.
static void SetClassParamExprs(std::string_view var_name,
                               const std::vector<DataType>& type_params,
                               SimContext& ctx) {
  if (type_params.empty()) return;
  std::vector<Expr*> exprs;
  exprs.reserve(type_params.size());
  for (const auto& tp : type_params) {
    exprs.push_back(tp.type_ref_expr);
  }
  ctx.SetVariableClassParamExprs(var_name, std::move(exprs));
}

// Handles `T v = new src;` shallow-copy construction. Returns true if `init`
// names a copyable source object and the copy was installed into `var_name`.
static bool TryExecClassShallowCopy(std::string_view var_name, const Expr* init,
                                    SimContext& ctx, Arena& arena) {
  if (!init->lhs || init->lhs->kind != ExprKind::kIdentifier) return false;
  auto src_val = EvalExpr(init->lhs, ctx, arena);
  auto* src_obj = ctx.GetClassObject(src_val.ToUint64());
  if (!src_obj) return false;
  auto* copy = src_obj->ShallowCopy(arena);
  auto copy_handle = ctx.AllocateClassObject(copy);
  auto* var = ctx.FindVariable(var_name);
  if (var) var->value = MakeLogic4VecVal(arena, 64, copy_handle);
  return true;
}

static bool TryExecClassVarDecl(const Stmt* stmt, SimContext& ctx,
                                Arena& arena) {
  auto class_type = stmt->var_decl_type.type_name;
  if (class_type.empty() || !ctx.FindClassType(class_type)) return false;
  ctx.CreateVariable(stmt->var_name, 64);
  ctx.SetVariableClassType(stmt->var_name, class_type);

  SetClassParamExprs(stmt->var_name, stmt->var_decl_type.type_params, ctx);

  if (!stmt->var_init) return true;

  // §8.8: an argument-less typed constructor call (`C c = D::new;`) constructs
  // the specified type D, not the declared handle type C. It parses as a bare
  // scope-resolved member access, so it is not a `new` call and must be
  // dispatched before the generic expression path, which cannot construct it.
  {
    Logic4Vec typed;
    if (TryEvalTypedConstructorNew(stmt->var_init, ctx, arena, typed)) {
      auto* var = ctx.FindVariable(stmt->var_name);
      if (var) var->value = typed;
      return true;
    }
  }

  // A class-handle initializer that is not a `new` call (e.g. a copy from
  // another handle or a static call such as `process::self()`) is evaluated
  // and stored like an ordinary assignment; only `new` needs the
  // construction/shallow-copy handling below.
  if (stmt->var_init->kind != ExprKind::kCall ||
      stmt->var_init->text != "new") {
    auto val = EvalExpr(stmt->var_init, ctx, arena);
    auto* var = ctx.FindVariable(stmt->var_name);
    if (var) var->value = val;
    return true;
  }

  if (TryExecClassShallowCopy(stmt->var_name, stmt->var_init, ctx, arena)) {
    return true;
  }

  auto handle = EvalClassNew(class_type, stmt->var_init, ctx, arena,
                             stmt->var_init->range.start);
  auto* var = ctx.FindVariable(stmt->var_name);
  if (var) var->value = handle;
  ApplyClassParamOverrides(stmt->var_name, handle.ToUint64(), ctx, arena);
  return true;
}

static Variable* CreateVarInScope(std::string_view name, uint32_t width,
                                  SimContext& ctx) {
  return ctx.HasLocalScope() ? ctx.CreateLocalVariable(name, width)
                             : ctx.CreateVariable(name, width);
}

static void CreateDeclVariable(const Stmt* stmt, uint32_t width, bool is_real,
                               SimContext& ctx, Arena& arena) {
  if (width == 0 && stmt->var_decl_type.kind == DataTypeKind::kString) {
    CreateVarInScope(stmt->var_name, 0, ctx);
    ctx.RegisterStringVariable(stmt->var_name);
  } else {
    if (width == 0) width = 32;
    if (is_real && width < 64) width = 64;
    CreateVarInScope(stmt->var_name, width, ctx);
    if (is_real) ctx.RegisterRealVariable(stmt->var_name);
    // §7.10: a queue dimension is not the range dimension of a fixed-size
    // unpacked array, so a declaration is one or the other and never both.
    if (!CreateBlockQueue(stmt, width, ctx, arena)) {
      CreateBlockArrayElements(stmt, width, ctx, arena);
    }
  }
}

// §13.3.2: all variables of a static task are static. A local with no explicit
// lifetime keyword inherits its enclosing subroutine's lifetime, so a plain
// local declared inside a static-lifetime task/function is itself static and
// must be a single cell shared across every activation -- including concurrent
// ones. Such a local therefore has to resolve against the shared static-frame
// store rather than the per-activation scope stack (which, since automatic and
// block locals are now private to each process, would otherwise give each
// concurrent activation its own copy). An explicit `automatic` local never
// becomes static.
static bool IsEffectivelyStaticLocal(const Stmt* stmt,
                                     std::string_view func_name,
                                     SimContext& ctx) {
  if (stmt->var_is_static) return true;
  if (stmt->var_is_automatic || func_name.empty()) return false;
  auto* f = ctx.FindFunction(func_name);
  return f && f->is_static && !f->is_automatic;
}

// Returns true if the declaration resolves to an already-existing variable
// (a static-func var to alias, or a local already present) and so needs no
// fresh creation.
static bool TryReuseExistingDeclVar(const Stmt* stmt,
                                    std::string_view func_name,
                                    SimContext& ctx) {
  if (IsEffectivelyStaticLocal(stmt, func_name, ctx) && !func_name.empty()) {
    auto* existing = ctx.FindStaticFuncVar(func_name, stmt->var_name);
    if (existing) {
      ctx.AliasLocalVariable(stmt->var_name, existing);
      return true;
    }
  } else if (!stmt->var_is_automatic) {
    if (ctx.HasLocalScope() && ctx.FindLocalVariable(stmt->var_name)) {
      return true;
    }
  }
  return false;
}

// §6.8's declared variable, as the declaration describes it rather than as the
// cell happens to have been created: the cell itself, the width the type asked
// for -- 0 where nothing could size it, which is not the carrier width
// CreateDeclVariable may have created the cell at -- and whether the type is
// one of the real family, whose initializer §6.12.1 converts rather than
// resizes. The three travel together because the initializer needs all of them
// to be assigned into the declared object rather than put in its place.
struct DeclaredObject {
  Variable* var;
  uint32_t declared_width;
  bool is_real;
};

// Applies 4-state coercion and the optional initializer to a freshly created
// variable, then records it as a static-func var when applicable.
//
// §6.8 executes a declaration's initializer "as if the assignment were made
// from an initial procedure", which §10.8 makes an assignment-like context, so
// §10.7 truncates or extends it into the width the declaration established. A
// Logic4Vec carries its own width, so writing the value straight over the
// variable put the expression's width in the declaration's place instead:
// `bit [3:0] v = 8'hFF;` in a procedural block left v eight bits reading 255.
// Lowerer::CoerceVarInitValue applies the same rule to a declaration at module
// scope and CreateFuncLocalVar to one in a subroutine body; a declaration in a
// procedural block runs here and had to be told it separately.
//
// The target is `declared_width`, the width the type asked for, rather than the
// width the variable was created at, and the two differ on exactly the cases
// this must leave alone. A type nothing could size is created at the 32-bit
// carrier CreateDeclVariable substitutes, and truncating to a carrier would cut
// a string reached through a typedef name (§6.16) down to the four characters
// 32 bits hold. A declared width of 0 says there is no width to resize to,
// which is what a string answers whether it is written bare or behind a name.
//
// A real is the one type whose created width is the target instead. §6.12.1
// converts an initializer that crosses the real/integer boundary rather than
// reinterpreting its bits, so `real r = 5;` has to hold the double 5.0; and
// `shortreal` declares 32 bits while being carried in the 64 that conversion
// needs. ConvertRealForKnownLhs performs the conversion, and resizes every
// value that does not cross the boundary.
//
// A declaration carrying an unpacked dimension is left as it was. Its variable
// is the element-width carrier that CreateBlockQueue and
// CreateBlockArrayElements size the real storage from rather than an object the
// initializer is assigned to, and `int a[3] = '{1,2,3}` evaluates to the
// ninety-six bits of a concatenation, which one element's width has nothing to
// say about.
static void InitializeDeclVariable(const Stmt* stmt, const DeclaredObject& obj,
                                   std::string_view func_name, SimContext& ctx,
                                   Arena& arena) {
  Variable* var = obj.var;
  var->is_4state = Is4stateType(stmt->var_decl_type.kind);
  if (!var->is_4state) CoerceTo2State(var->value);
  if (stmt->var_init) {
    Logic4Vec val = EvalExpr(stmt->var_init, ctx, arena);
    if (stmt->var_unpacked_dims.empty()) {
      uint32_t target = obj.is_real ? var->value.width : obj.declared_width;
      val = ConvertRealForKnownLhs(val, obj.is_real, target, arena);
    }
    var->value = val;
    if (!var->is_4state) CoerceTo2State(var->value);
  }

  if (IsEffectivelyStaticLocal(stmt, func_name, ctx) && !func_name.empty()) {
    ctx.SaveStaticFuncVar(func_name, stmt->var_name, var);
  }
}

StmtResult ExecVarDeclImpl(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (TryExecWeakRefVarDecl(stmt, ctx, arena)) return StmtResult::kDone;
  if (TryExecClassVarDecl(stmt, ctx, arena)) return StmtResult::kDone;

  auto func_name = ctx.CurrentFuncName();
  if (TryReuseExistingDeclVar(stmt, func_name, ctx)) return StmtResult::kDone;

  // §6.18: a variable declared with a user-defined type name is an object of
  // the type that name stands for, so `nib v` is as wide as `nib` is.
  // DeclaredTypeWidth is what reaches that width, asking the elaborated typedef
  // table for a DataTypeKind::kNamed; the one-argument EvalTypeWidth gives such
  // a type no width at all, and CreateDeclVariable's `width == 0` fallback then
  // made every typedef'd local 32 bits. A type the table cannot size still
  // answers 0 and still reaches that fallback, and a string (§6.16) still
  // reaches the branch above it, because DeclaredTypeWidth answers 0 for a
  // string typedef as well as for a bare one.
  uint32_t width = DeclaredTypeWidth(stmt->var_decl_type, ctx);
  bool is_real = (stmt->var_decl_type.kind == DataTypeKind::kReal ||
                  stmt->var_decl_type.kind == DataTypeKind::kShortreal ||
                  stmt->var_decl_type.kind == DataTypeKind::kRealtime);
  CreateDeclVariable(stmt, width, is_real, ctx, arena);
  RecordVariableEnumType(stmt->var_name, stmt->var_decl_type, ctx);
  auto* var = ctx.FindVariable(stmt->var_name);
  if (var) {
    InitializeDeclVariable(stmt, {var, width, is_real}, func_name, ctx, arena);
  }
  return StmtResult::kDone;
}

static void CollectExprVars(const Expr* expr, SimContext& ctx,
                            std::vector<Variable*>& vars) {
  if (!expr) return;
  if (expr->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->text);
    if (var) vars.push_back(var);
    return;
  }
  CollectExprVars(expr->lhs, ctx, vars);
  CollectExprVars(expr->rhs, ctx, vars);
  CollectExprVars(expr->condition, ctx, vars);
  CollectExprVars(expr->true_expr, ctx, vars);
  CollectExprVars(expr->false_expr, ctx, vars);
  CollectExprVars(expr->base, ctx, vars);
  CollectExprVars(expr->index, ctx, vars);
  CollectExprVars(expr->index_end, ctx, vars);
  CollectExprVars(expr->with_expr, ctx, vars);
  CollectExprVars(expr->repeat_count, ctx, vars);
  for (auto* e : expr->elements) CollectExprVars(e, ctx, vars);
  for (auto* a : expr->args) CollectExprVars(a, ctx, vars);
}

// Returns the distinct variables referenced by `rhs`, excluding `self`.
static std::vector<Variable*> CollectDistinctRhsVars(const Expr* rhs,
                                                     SimContext& ctx,
                                                     Variable* self) {
  std::vector<Variable*> rhs_vars;
  CollectExprVars(rhs, ctx, rhs_vars);
  std::sort(rhs_vars.begin(), rhs_vars.end());
  rhs_vars.erase(std::unique(rhs_vars.begin(), rhs_vars.end()), rhs_vars.end());
  rhs_vars.erase(std::remove(rhs_vars.begin(), rhs_vars.end(), self),
                 rhs_vars.end());
  return rhs_vars;
}

// Behavior of the watchers InstallRhsWatchers installs, and of the write each
// installer makes before installing them: `still_valid` gates the watcher
// (returning true to detach once its backing force/assign is no longer in
// effect); `forced` selects whether the value written also refreshes
// var->forced_value.
struct RhsWatcherSpec {
  std::function<bool()> still_valid;
  bool forced = false;
  // §10.6.2: the net the force is standing on, when the target is one. Its
  // reported strength is the force's while the force is in effect, so a
  // recomputed forced value re-resolves it; null when the target is a variable,
  // which carries no strength.
  Net* net = nullptr;
  // §10.7: "The size of the left-hand side of an assignment forms the context
  // for the right-hand expression", so a right-hand side that is evaluated
  // again later has to be evaluated in the same context or the two evaluations
  // answer differently. Zero leaves the expression self-determined, which is
  // what every singular target asks for and what the force path has always
  // done.
  uint32_t rhs_width = 0;
  // §11.4.12 treats a concatenation as "a packed vector of bits", so an element
  // of one owns a window of the right-hand value and a window of its own
  // storage, and the two are unrelated numbers: `bus[3]` in `{w, bus[3]}` takes
  // bit 0 of the value and lands on bit 3 of `bus`. A width of zero is the
  // whole of it, which is the singular target: it owns every bit of the value
  // and every bit of itself.
  uint32_t src_lo = 0;
  uint32_t src_width = 0;
  uint32_t dst_lo = 0;
  uint32_t dst_width = 0;
};

// Writes into `var` the part of `val` this installation owns. A singular target
// owns the whole value and takes it whole, width and all. An element of a
// concatenation owns the two windows above instead, and the bits outside its
// destination window belong to the other elements or to nothing at all and have
// to be left standing, which is what DepositBitField does and what writing the
// variable whole did not: `force {w, bus[3]} = 2'b11;` gave `bus` the whole
// two-bit value.
//
// The deposit is made into a fresh copy of the target's current value rather
// than through the words it is holding. Copying a Logic4Vec copies its `words`
// pointer rather than the words (common/types.h), so a variable last written
// whole from another object shares that object's storage, and depositing
// through the pointer would write these bits into whatever else is holding it.
//
// WriteBitSelect resolves the same window for a select and is deliberately not
// the writer here: it declines every write to a forced variable, and the force
// whose bits these are has just set that flag, so the deposit would be dropped
// and the element would keep the value it had.
static void WriteOwnedBits(Variable* var, const Logic4Vec& val,
                           const RhsWatcherSpec& spec, Arena& arena) {
  if (spec.dst_width == 0) {
    if (spec.forced) var->forced_value = val;
    var->value = val;
  } else {
    Logic4Vec updated = ExtractBitField(arena, var->value, 0, var->value.width);
    DepositBitField(
        updated, spec.dst_lo,
        spec.src_width == 0
            ? val
            : ExtractBitField(arena, val, spec.src_lo, spec.src_width),
        spec.dst_width);
    var->value = updated;
    if (spec.forced) var->forced_value = var->value;
  }
  if (!var->is_4state) CoerceTo2State(var->value);
}

// Recomputes `rhs` into the part of `var` the spec's windows name, also
// refreshing var->forced_value when the spec is a forced one.
static void RecomputeRhsInto(Variable* var, const Expr* rhs, SimContext& ctx,
                             Arena& arena, const RhsWatcherSpec& spec) {
  auto new_val = EvalExpr(rhs, ctx, arena, spec.rhs_width);
  WriteOwnedBits(var, new_val, spec, arena);
  var->NotifyWatchers();
}

// Installs, on each variable referenced by `rhs` (other than `var`), a watcher
// that re-evaluates `rhs` into `var` whenever a source changes.
static void InstallRhsWatchers(Variable* var, const Expr* rhs, SimContext& ctx,
                               Arena& arena, const RhsWatcherSpec& spec) {
  auto* ctx_ptr = &ctx;
  auto* arena_ptr = &arena;
  for (auto* rhs_var : CollectDistinctRhsVars(rhs, ctx, var)) {
    rhs_var->AddWatcher([var, rhs, ctx_ptr, arena_ptr, spec]() {
      if (!spec.still_valid()) return true;
      RecomputeRhsInto(var, rhs, *ctx_ptr, *arena_ptr, spec);
      if (spec.net != nullptr) spec.net->Resolve(*arena_ptr);
      return false;
    });
  }
}

// Applies a procedural continuous-assignment forced value to `var` from the
// expression `rhs`, then installs watchers on each variable appearing in `rhs`
// so the forced value is re-evaluated whenever those variables change. The spec
// carries the net the target stands on and, for an element of a concatenation
// target, the windows that element owns; this fills in the rest of it.
static void InstallForcedValueWatcher(Variable* var, const Expr* rhs,
                                      SimContext& ctx, Arena& arena,
                                      RhsWatcherSpec spec) {
  spec.forced = true;
  auto rhs_val = EvalExpr(rhs, ctx, arena, spec.rhs_width);
  var->is_forced = true;
  WriteOwnedBits(var, rhs_val, spec, arena);
  var->proc_cont_rhs = rhs;
  var->NotifyWatchers();

  // §10.6.2: the force overrides the net's drivers from here, so the strength
  // it reports is settled now rather than at the next driver update -- there
  // may be no further one, and a net forced before anything drove it has no
  // strength recorded at all.
  if (spec.net != nullptr) spec.net->Resolve(arena);

  spec.still_valid = [var, rhs]() {
    return var->is_forced && var->proc_cont_rhs == rhs;
  };
  InstallRhsWatchers(var, rhs, ctx, arena, spec);
}

// Reestablishes a continuous assignment on `var` from expression `rhs` after
// a release statement. Similar to InstallForcedValueWatcher but for
// assignments: does not set is_forced, and watchers check assign_cont_rhs
// instead of is_forced to remain valid after release.
static void ReestablishContinuousAssignment(Variable* var, const Expr* rhs,
                                            SimContext& ctx, Arena& arena,
                                            RhsWatcherSpec spec) {
  // §10.6.1 gives the assign statement "a singular variable reference or a
  // concatenation of variables", so nothing it reestablishes stands on a net
  // and the force's net does not carry over into the assignment that outlives
  // it.
  spec.net = nullptr;
  spec.forced = false;
  auto rhs_val = EvalExpr(rhs, ctx, arena, spec.rhs_width);
  WriteOwnedBits(var, rhs_val, spec, arena);
  var->NotifyWatchers();

  spec.still_valid = [var, rhs]() {
    return var->assign_cont_rhs && var->assign_cont_rhs == rhs;
  };
  InstallRhsWatchers(var, rhs, ctx, arena, spec);
}

// One element of a concatenation left-hand side, the window of the right-hand
// value it owns and the width that value is evaluated at. §11.4.12 makes the
// concatenation "a packed vector of bits", so the rightmost element takes the
// least significant bits and each element to its left begins where the previous
// one ended: `src_lo` is where this one begins and `width` is what
// ConcatLhsElemWidth gave it.
struct ConcatElemSlot {
  const Expr* el = nullptr;
  Variable* var = nullptr;
  uint32_t src_lo = 0;
  uint32_t width = 0;
  uint32_t rhs_width = 0;
};

// The window of the right-hand value `slot` owns and the window of its own
// storage that receives it. A whole-variable element takes its bits into the
// whole of itself; a select element takes them into the bits §11.5.1 says its
// indices address, "determined by the declaration".
//
// The two windows are two answers and not one: the element is as wide as
// ConcatLhsElemWidth makes it whether or not its address is in bounds, and it
// writes only the bits SelectStorageBits leaves it. They differ for a
// part-select that is partly out of range, which §11.5.1 has "when written,
// only affect the bits that are in range" -- `a[9:6]` on `logic [7:0] a` is
// four bits of the concatenation landing on the two of them that exist. An
// empty window never reaches here: ApplyToConcatElement declines the element
// first, so the dst_width of zero below still means the whole variable.
static RhsWatcherSpec SpecForSlot(const ConcatElemSlot& slot, SimContext& ctx,
                                  Arena& arena) {
  PartSelectBits dst{0, slot.width};
  if (slot.el->kind == ExprKind::kSelect && slot.el->base != nullptr)
    dst = SelectStorageBits(*slot.var, slot.el, ctx, arena);
  // §10.6.2 makes force a statement on a net as well as on a variable, and the
  // net is what holds the strength the force settles, so only an element naming
  // a whole net is looked up. A select element is left standing on no net, as
  // the standalone `force bus[3] = 1'b1;` is: ctx.FindNet on the select's base
  // would hand Net::Resolve the whole of `bus`, which settles every bit of it
  // from the drivers and would undo the one bit this element forced.
  Net* net = slot.el->kind == ExprKind::kIdentifier ? ctx.FindNet(slot.el->text)
                                                    : nullptr;
  RhsWatcherSpec spec;
  spec.net = net;
  spec.rhs_width = slot.rhs_width;
  spec.src_lo = slot.src_lo;
  spec.src_width = slot.width;
  spec.dst_lo = dst.lo;
  spec.dst_width = dst.width;
  return spec;
}

// Forces or assigns one element of a concatenation target. §10.6.1's assign and
// §10.6.2's force share this executor and differ here only in that the assign
// records its right-hand side, which a later deassign or release looks for.
//
// One residual this does not fix: is_forced is a single flag on the whole
// Variable, so `force {w, bus[3]} = 2'b11;` puts the right bits in the right
// place and still marks the whole of `bus` forced, suppressing every driver of
// every bit of it rather than of bit 3 alone. That is #3512, and it is a change
// to what Variable records rather than to this walk.
static void ForceOneElement(const ConcatElemSlot& slot, const Stmt* stmt,
                            SimContext& ctx, Arena& arena) {
  if (stmt->kind == StmtKind::kAssign) slot.var->assign_cont_rhs = stmt->rhs;
  InstallForcedValueWatcher(slot.var, stmt->rhs, ctx, arena,
                            SpecForSlot(slot, ctx, arena));
}

// Releases or deassigns one element of a concatenation target. §10.6.1: "The
// deassign procedural statement shall end an assign procedural continuous
// assignment to a variable", and §10.6.2 ends a force on a release; each
// element was marked on its own and so is cleared on its own.
static void ReleaseOneElement(const ConcatElemSlot& slot, const Stmt* stmt,
                              SimContext& ctx, Arena& arena) {
  Variable* var = slot.var;
  var->is_forced = false;
  var->proc_cont_rhs = nullptr;
  if (stmt->kind == StmtKind::kDeassign) {
    var->assign_cont_rhs = nullptr;
    return;
  }

  RhsWatcherSpec spec = SpecForSlot(slot, ctx, arena);
  // §10.6.2: "When released, the net shall immediately be assigned the value
  // determined by the drivers of the net."
  if (spec.net != nullptr) spec.net->Resolve(arena);

  // §10.6.1: "Releasing a variable that is driven by a continuous assignment or
  // currently has an active assign procedural continuous assignment shall
  // reestablish that assignment", and the element gets back the window of that
  // assignment's value it held, not the whole of it: without the window,
  // `assign {a, b} = 16'h1234; force {a, b} = ...; release {a, b};` handed `a`
  // the entire sixteen-bit value.
  //
  // The window is this release statement's own, since the variable records the
  // assignment's right-hand side and not the window it was installed with, so a
  // release naming a target written differently from the assign's reestablishes
  // through its own windows. That is #3526, and answering it is a change to
  // what Variable records rather than to this walk.
  if (var->assign_cont_rhs)
    ReestablishContinuousAssignment(var, var->assign_cont_rhs, ctx, arena,
                                    spec);
}

// Routes one element to the statement that named it: the two statements that
// install a procedural continuous assignment, and the two that end one.
//
// An element addressing no bit of its target is routed nowhere. §11.5.1 gives
// such a write "no effect on the data stored", and for these four statements
// that has to mean the target is left exactly as it was found: is_forced is one
// flag on the whole Variable, so setting it for an element owning none of its
// bits would suppress every driver of every bit of it, and the watchers
// installed with it would go on recomputing a value into it. The element has
// already taken its own width of the right-hand value, which is what the caller
// advances past.
static void ApplyToConcatElement(const ConcatElemSlot& slot, const Stmt* stmt,
                                 SimContext& ctx, Arena& arena) {
  if (!ConcatLhsElemHasWritableBits(slot.el, *slot.var, ctx, arena)) return;
  if (stmt->kind == StmtKind::kRelease || stmt->kind == StmtKind::kDeassign) {
    ReleaseOneElement(slot, stmt, ctx, arena);
    return;
  }
  ForceOneElement(slot, stmt, ctx, arena);
}

// Distributes a force, an assign, a release or a deassign over the elements of
// a concatenation target. §10.6.2 admits "a concatenation of these" and §10.6.1
// "a concatenation of variables", so each element is a target of the statement
// in its own right and the elements divide the right-hand value the way
// §11.4.12 divides it for a blocking assignment: the walk runs in reverse so
// that the rightmost element takes the least significant bits. Returns the
// offset one past the elements it walked, which is where a nesting caller
// resumes. All four statements walk here, so a release draws the element
// boundaries exactly where the force drew them.
//
// An element ConcatLhsElemWidth cannot size is passed over without advancing
// the offset, which is what UnpackConcatLhs does with the same element on the
// blocking path. Nothing here knows its width to be anything else, so no other
// advance is available, and a force and an assignment to such a target misalign
// the elements to its left together rather than disagreeing.
//
// A select addressing no bit of its object is not that element: §11.5.1 gives
// it the width its indices name and no bits of its target to write, so the
// offset advances past it and ApplyToConcatElement declines it.
static uint32_t WalkConcatLhsElements(const Expr* lhs, const Stmt* stmt,
                                      uint32_t bit_offset, SimContext& ctx,
                                      Arena& arena) {
  uint32_t rhs_width = LhsContextWidth(stmt->lhs, ctx);
  for (auto it = lhs->elements.rbegin(); it != lhs->elements.rend(); ++it) {
    const Expr* el = *it;
    uint32_t w = ConcatLhsElemWidth(el, ctx, arena);
    if (w == 0) continue;
    // §11.4.12: a nested concatenation lvalue divides the slice it was given
    // among its own elements, so the walk continues into it at the offset it
    // has reached.
    if (IsConcatLhs(el)) {
      bit_offset = WalkConcatLhsElements(UnwrapTypedPattern(el), stmt,
                                         bit_offset, ctx, arena);
      continue;
    }
    if (auto* var = ResolveLhsVariable(el, ctx))
      ApplyToConcatElement({el, var, bit_offset, w, rhs_width}, stmt, ctx,
                           arena);
    bit_offset += w;
  }
  return bit_offset;
}

StmtResult ExecForceOrAssignImpl(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;
  // §10.6.2: "The left-hand side of the assignment can be a reference to a
  // singular variable, a net, a constant bit-select of a vector net, a constant
  // part-select of a vector net, or a concatenation of these", and §10.6.1
  // gives the assign statement "a singular variable reference or a
  // concatenation of variables". A concatenation names no one object, so
  // ResolveLhsVariable answers null for it and the statement returned below
  // having marked nothing and written nothing: `force {a, b} = 16'h1234;` left
  // `a` and `b` at their initial values with is_forced clear on both.
  if (IsConcatLhs(stmt->lhs)) {
    WalkConcatLhsElements(UnwrapTypedPattern(stmt->lhs), stmt, 0, ctx, arena);
    return StmtResult::kDone;
  }
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (!var) return StmtResult::kDone;

  if (stmt->kind == StmtKind::kAssign) var->assign_cont_rhs = stmt->rhs;
  // §10.6.2 makes force a statement on a net as well as on a variable, and the
  // net is what holds the strength the force settles. A select or a
  // concatenation target names no net here, the same way a continuous
  // assignment's does not.
  Net* net = stmt->lhs->kind == ExprKind::kIdentifier
                 ? ctx.FindNet(stmt->lhs->text)
                 : nullptr;
  RhsWatcherSpec spec;
  spec.net = net;
  InstallForcedValueWatcher(var, stmt->rhs, ctx, arena, spec);

  return StmtResult::kDone;
}

StmtResult ExecReleaseOrDeassignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;
  // §10.6.1 and §10.6.2 give release and deassign the same targets their
  // installing statements take, so a concatenation is ended element by element.
  // Resolving it as one object answered null, which left `release {a, b};` and
  // `deassign {a, b};` as no-ops and would have made the force above one no
  // release could lift.
  if (IsConcatLhs(stmt->lhs)) {
    WalkConcatLhsElements(UnwrapTypedPattern(stmt->lhs), stmt, 0, ctx, arena);
    return StmtResult::kDone;
  }
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (!var) return StmtResult::kDone;

  var->is_forced = false;
  var->proc_cont_rhs = nullptr;

  if (stmt->kind == StmtKind::kDeassign) {
    var->assign_cont_rhs = nullptr;
  } else if (stmt->lhs->kind == ExprKind::kIdentifier) {
    if (auto* net = ctx.FindNet(stmt->lhs->text)) {
      net->Resolve(arena);
    }
  }

  if (var->assign_cont_rhs && stmt->kind != StmtKind::kDeassign) {
    ReestablishContinuousAssignment(var, var->assign_cont_rhs, ctx, arena, {});
  }

  return StmtResult::kDone;
}

}  // namespace delta
