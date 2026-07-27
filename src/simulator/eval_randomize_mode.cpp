#include <algorithm>
#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

// 18.8: report whether a random variable is active on this object. Every
// rand/randc variable is active when the object is created, so an absent entry
// means active; an explicit entry records the last rand_mode() setting.
bool IsObjectRandActive(const ClassObject* obj, std::string_view name) {
  auto it = obj->rand_active.find(std::string(name));
  return it == obj->rand_active.end() ? true : it->second;
}

// 18.6.2: post_randomize() is invoked by randomize() after the new random
// values have been computed AND assigned back to the object, so a user
// post_randomize() reads the just-randomized members at their new values. It is
// therefore called by the caller only after WriteBackSolved has published the
// solved values, and only on a successful solve (18.6.3 skips it on failure).
// Like pre_randomize() it is resolved on the dynamic class, giving the same
// apparent-virtual and inherited-implementation behavior.
void InvokePostRandomize(ClassObject* obj, const Expr* expr, SimContext& ctx,
                         Arena& arena) {
  const ClassTypeInfo* owner = nullptr;
  if (ModuleItem* post =
          obj->ResolveMethodForType("post_randomize", obj->type, &owner)) {
    ctx.PushMethodClass(owner);
    ExecInstanceMethodCall(post, obj, expr, ctx, arena);
    ctx.PopMethodClass();
  }
}

// 18.6.1: enumerate the rand/randc class-handle members visible on the object.
// Each such member names a sub-object: because randomize() sets "all the random
// variables and objects", every referenced object is randomized in turn. Walk
// the inheritance chain so inherited random object handles are included.
void CollectRandObjectMembers(const ClassTypeInfo* type, SimContext& ctx,
                              std::vector<std::string>& out) {
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kProperty &&
          (m->is_rand || m->is_randc) && IsClassHandleMember(m, ctx))
        out.push_back(std::string(m->name));
    }
  }
}

// 18.11/18.11.1: what a randomize() argument list designates -- the named
// object properties that make up the active random set, whether a list was
// written at all, and whether the special `null` argument was passed.
struct InlineRandomArgs {
  std::unordered_set<std::string> names;
  bool has_list;
  bool null_checker;
};

// 18.11: a randomize() argument list names the object properties that make up
// the active random set for this call. An unnamed rand variable becomes a state
// variable and a named non-random property becomes a random one.
//
// 18.11.1: the special argument null designates no random variables for the
// duration of the call -- every class member, even one declared rand or randc,
// behaves as a state variable. This turns randomize() into an inline constraint
// checker that evaluates all constraints against the current values and returns
// 1 when they all hold and 0 otherwise, drawing no new value. An empty (but
// present) active set realizes exactly that.
InlineRandomArgs CollectInlineRandomArgs(const Expr* expr) {
  InlineRandomArgs args{{}, false, false};
  for (const Expr* arg : expr->args) {
    if (arg != nullptr && arg->kind == ExprKind::kIdentifier &&
        arg->text == "null") {
      args.names.clear();
      args.has_list = false;
      args.null_checker = true;
      return args;
    }
    std::string_view nm = InlineRandomArgName(arg);
    if (!nm.empty()) {
      args.names.insert(std::string(nm));
      args.has_list = true;
    }
  }
  return args;
}

bool TryEvalRandomizeMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (parts.method_name != "randomize") return false;
  ClassObject* obj = ResolveRandomizeTarget(ctx, parts);
  if (!obj) return false;

  // 18.11: a randomize() argument list names the object properties that make up
  // the active random set for this call. Collect those names; an unnamed rand
  // variable becomes a state variable and a named non-random property becomes a
  // random one.
  //
  // 18.11.1: the special argument null designates no random variables for the
  // duration of the call -- every class member, even one declared rand or
  // randc, behaves as a state variable. This turns randomize() into an inline
  // constraint checker that evaluates all constraints against the current
  // values and returns 1 when they all hold and 0 otherwise, drawing no new
  // value. An empty (but present) active set realizes exactly that: no variable
  // is in it, so each is disabled and held at its current value in
  // RandomizeObject, and the null_checker flag additionally holds any rand
  // sub-object as state.
  InlineRandomArgs args = CollectInlineRandomArgs(expr);
  const std::unordered_set<std::string>& inline_random = args.names;
  bool has_inline_list = args.has_list;
  bool null_checker = args.null_checker;

  std::unordered_set<const ClassObject*> visited;
  // 18.5.8: the plain randomize() form randomizes the object together with all
  // of its active random object members as a single whole, so global
  // constraints relating variables from different objects are solved
  // simultaneously. When the active random object set (rule a) has more than
  // the root object, solve the tree jointly. The argument-list form (18.11),
  // the null checker (18.11.1) and an inline (with) block keep the per-object
  // path.
  if (!null_checker && !has_inline_list && expr->inline_constraint == nullptr) {
    std::vector<JointObject> objects;
    CollectActiveRandomObjects(obj, "", ctx, objects, visited);
    if (objects.size() > 1) {
      bool ok = RandomizeObjectTree(ctx, arena, expr, objects);
      out = MakeLogic4VecVal(arena, 32, ok ? 1 : 0);
      return true;
    }
    visited.clear();
  }
  const std::unordered_set<std::string>* active_set =
      (null_checker || has_inline_list) ? &inline_random : nullptr;
  bool solved = RandomizeObject(
      obj, ctx, arena,
      {expr, expr->inline_constraint, active_set, null_checker}, visited);
  out = MakeLogic4VecVal(arena, 32, solved ? 1 : 0);
  return true;
}

namespace {

// 18.12: recognize the scope randomize function. It is spelled
// std::randomize(), or -- outside a class method, where a bare `randomize`
// would instead name the class's own built-in method -- simply randomize(). The
// parser leaves the callee as a plain identifier for the bare form and as a
// `std::randomize` member access for the qualified form.
bool IsScopeRandomizeForm(const Expr* expr, SimContext& ctx) {
  if (expr == nullptr || expr->kind != ExprKind::kCall || expr->lhs == nullptr)
    return false;
  const Expr* callee = expr->lhs;
  if (callee->kind == ExprKind::kMemberAccess && callee->rhs != nullptr &&
      callee->rhs->kind == ExprKind::kIdentifier &&
      callee->rhs->text == "randomize" && callee->lhs != nullptr &&
      callee->lhs->kind == ExprKind::kIdentifier && callee->lhs->text == "std")
    return true;
  if (callee->kind == ExprKind::kIdentifier && callee->text == "randomize" &&
      ctx.CurrentMethodClass() == nullptr && ctx.CurrentThis() == nullptr)
    return true;
  return false;
}

}  // namespace

bool TryEvalScopeRandomizeCall(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  if (!IsScopeRandomizeForm(expr, ctx)) return false;

  // 18.12: each named scope variable is a rand variable whose domain spans its
  // declared width, with its current value seeded so a failed solve can leave
  // it unchanged.
  std::vector<RandInfo> MakeScopeRandVariables(
      const std::vector<Variable*>& targets,
      const std::vector<std::string>& names) {
    std::vector<RandInfo> rands;
    rands.reserve(targets.size());
    for (size_t i = 0; i < targets.size(); ++i) {
      uint32_t w = targets[i]->value.width;
      if (w == 0) w = 32;
      RandInfo ri;
      ri.name = names[i];
      ri.var.name = names[i];
      ri.var.width = w;
      ri.var.min_val = 0;
      ri.var.max_val = (w >= 63) ? INT64_MAX : ((int64_t{1} << w) - 1);
      ri.var.value = static_cast<int64_t>(targets[i]->value.ToUint64());
      rands.push_back(std::move(ri));
    }
    return rands;
  }

  // 18.12.1: the std::randomize() with { constraint_block } form adds inline
  // constraints to the scope solve. The arguments named in the call are the
  // random variables; every other variable a constraint mentions is a state
  // variable, held at its current value and read as a constant. Translating
  // each captured relation against the argument rand set realizes exactly that
  // split: a name in the argument list binds as a solver variable, while an
  // unlisted scope variable is evaluated in place through the ordinary scope
  // lookup and enters the constraint as its present value. This reuses the
  // class randomize with-block translation (18.7).
  std::vector<ConstraintExpr> TranslateScopeWithBlock(
      const Expr* expr, std::vector<RandInfo>& rands, RandomizeCtx& rc) {
    std::vector<ConstraintExpr> with_constraints;
    if (expr->inline_constraint == nullptr) return with_constraints;
    with_constraints.reserve(expr->inline_constraint->constraint_exprs.size());
    for (const Expr* rel : expr->inline_constraint->constraint_exprs)
      with_constraints.push_back(TranslateRelation(rel, rands, rc));
    return with_constraints;
  }

  // Write each drawn value back to the scope variable it was solved for.
  void WriteBackScopeSolved(const std::vector<Variable*>& targets,
                            const std::vector<std::string>& names,
                            const ConstraintSolver& solver, Arena& arena) {
    for (size_t i = 0; i < targets.size(); ++i) {
      uint32_t w = targets[i]->value.width;
      if (w == 0) w = 32;
      targets[i]->value = MakeLogic4VecVal(
          arena, w, static_cast<uint64_t>(solver.GetValue(names[i])));
    }
  }

  // 18.12: the arguments specify the variables of the current scope that are to
  // be assigned random values. Resolve each to a live scope variable; a
  // non-identifier argument is not a form this scope randomize path services,
  // so defer to ordinary dispatch rather than misfire.
  std::vector<Variable*> targets;
  std::vector<std::string> names;
  for (const Expr* arg : expr->args) {
    if (arg == nullptr || arg->kind != ExprKind::kIdentifier) return false;
    Variable* var = ctx.FindVariable(arg->text);
    if (var == nullptr) return false;
    targets.push_back(var);
    names.emplace_back(arg->text);
  }

  // 18.12: called with no argument, the scope randomize does not change the
  // value of any variable and instead checks its constraints, returning 1 when
  // all of them hold. Without a with constraint_block (that form is 18.12.1)
  // there is no constraint expression to evaluate to false, so the checker
  // takes the "otherwise" branch and returns 1, leaving every variable
  // untouched.
  if (targets.empty()) {
    out = MakeLogic4VecVal(arena, 32, 1);
    return true;
  }

  // 18.12: the scope randomize behaves exactly as a class randomize method,
  // only over the current scope's variables. Seed from the active per-process
  // generator so the draw is fresh and thread-stable (18.14.2). Each named
  // variable is a rand variable whose domain spans its declared width, and its
  // current value is seeded so a failed solve can leave it unchanged.
  ConstraintSolver solver(static_cast<uint32_t>(ctx.ActiveRng()()));
  std::vector<RandInfo> rands = MakeScopeRandVariables(targets, names);

  // 18.12.1: the std::randomize() with { constraint_block } form adds inline
  // constraints to the scope solve. The arguments named in the call are the
  // random variables; every other variable a constraint mentions is a state
  // variable, held at its current value and read as a constant. Translating
  // each captured relation against the argument rand set realizes exactly that
  // split: a name in the argument list binds as a solver variable, while an
  // unlisted scope variable is evaluated in place through the ordinary scope
  // lookup and enters the constraint as its present value. This reuses the
  // class randomize with-block translation (18.7); a scope randomize has no
  // receiver object, so the RandomizeCtx carries a null 'this' -- the
  // scope-variable reads it drives never need one.
  RandomizeCtx rc{nullptr, ctx, arena};
  std::vector<ConstraintExpr> with_constraints =
      TranslateScopeWithBlock(expr, rands, rc);

  for (auto& ri : rands) {
    // A with-block bound may have folded the domain past its own limit (e.g.
    // two opposing bounds); keep it well-formed before handing it to the
    // solver.
    if (ri.var.min_val > ri.var.max_val) ri.var.max_val = ri.var.min_val;
    solver.AddVariable(ri.var);
  }

  bool ok = solver.SolveWith(with_constraints);

  // 18.12: the call returns 1 only when it successfully sets all the random
  // variables to valid values, in which case each drawn value is written back;
  // otherwise it returns 0. 18.6.3: on failure the variables retain their
  // previous values, so nothing is written back.
  if (ok) WriteBackScopeSolved(targets, names, solver, arena);
  out = MakeLogic4VecVal(arena, 32, ok ? 1 : 0);
  return true;
}

bool TryEvalObjectSrandom(const Expr* expr, SimContext& ctx, Arena& arena,
                          Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (parts.method_name != "srandom") return false;
  ClassObject* obj = ResolveRandomizeTarget(ctx, parts);
  if (!obj) return false;

  // §18.13.3: srandom() seeds the object's own RNG with the given seed. The
  // argument is an int, so evaluate it and narrow to the 32-bit seed. Resetting
  // the object's stream here makes a following randomize() replay the sequence
  // keyed by `seed` (§18.14 object stability).
  uint32_t seed = 0;
  if (!expr->args.empty()) {
    seed =
        static_cast<uint32_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  }
  ctx.SeedObjectRng(obj, seed);
  out = MakeLogic4VecVal(arena, 1, 0);
  return true;
}

bool TryEvalObjectGetRandState(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (parts.method_name != "get_randstate") return false;
  ClassObject* obj = ResolveRandomizeTarget(ctx, parts);
  if (!obj) return false;

  // §18.13.4: return the object's current RNG state as a string. The state is
  // of implementation-dependent length and format; here it is the mt19937
  // serialization, packed so it round-trips through a string-typed variable and
  // back into set_randstate().
  out = StringToLogic4Vec(arena, ctx.GetRandState(obj));
  return true;
}

bool TryEvalObjectSetRandState(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (parts.method_name != "set_randstate") return false;
  ClassObject* obj = ResolveRandomizeTarget(ctx, parts);
  if (!obj) return false;

  // §18.13.5: install the given string as the object's RNG internal state,
  // overwriting whatever the generator held. The argument is a string, so read
  // its raw bytes back before handing it to the deserializer. set_randstate()
  // returns void.
  std::string state;
  if (!expr->args.empty()) {
    state = Logic4VecToString(EvalExpr(expr->args[0], ctx, arena));
  }
  ctx.SetRandState(obj, state);
  out = MakeLogic4VecVal(arena, 1, 0);
  return true;
}

// 18.9: a constraint_mode() call with no constraint identifier applies to every
// constraint block in the object's class hierarchy.
void SetAllConstraintsActive(ClassObject* obj, bool on) {
  for (const auto* lvl = obj->type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kConstraint)
        SetObjectConstraintActive(obj, m->name, on);
    }
  }
}

// 18.8: a rand_mode() call with no variable name applies to every rand/randc
// variable in the object's class hierarchy.
void SetAllRandVariablesActive(ClassObject* obj, bool on) {
  for (const auto* lvl = obj->type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kProperty && (m->is_rand || m->is_randc))
        SetObjectRandActive(obj, m->name, on);
    }
  }
}

bool TryEvalObjectConstraintMode(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  std::string_view obj_name;
  std::string_view constraint_name;
  if (!ExtractConstraintModeParts(expr, obj_name, constraint_name))
    return false;
  MethodCallParts parts;
  parts.var_name = obj_name;
  ClassObject* obj = ResolveRandomizeTarget(ctx, parts);
  if (!obj) return false;

  // 18.9 nonvoid form: called with no argument, constraint_mode() returns the
  // current active state of the named block -- 1 (ON) when active, 0 (OFF) when
  // inactive.
  if (expr->args.empty()) {
    bool active = IsObjectConstraintActive(obj, constraint_name);
    out = MakeLogic4VecVal(arena, 32, active ? 1 : 0);
    return true;
  }

  // 18.9 / Table 18-4 void form: the argument selects ON (nonzero) or OFF
  // (zero). A named call sets that one block; a call with no constraint
  // identifier applies to every constraint block in the object's class
  // hierarchy.
  bool on = EvalExpr(expr->args[0], ctx, arena).ToUint64() != 0;
  if (constraint_name.empty()) {
    SetAllConstraintsActive(obj, on);
  } else {
    SetObjectConstraintActive(obj, constraint_name, on);
  }
  out = MakeLogic4VecVal(arena, 1, 0);
  return true;
}

bool TryEvalObjectRandMode(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  std::string_view obj_name;
  std::string_view var_name;
  if (!ExtractRandModeParts(expr, obj_name, var_name)) return false;
  MethodCallParts parts;
  parts.var_name = obj_name;
  ClassObject* obj = ResolveRandomizeTarget(ctx, parts);
  if (!obj) return false;

  // 18.8 nonvoid form: called with no argument, rand_mode() returns the current
  // active state of the named variable -- 1 (ON) when active, 0 (OFF) when
  // inactive. This form must name a variable; a no-name query matches neither
  // form, so leave it for normal dispatch.
  if (expr->args.empty()) {
    if (var_name.empty()) return false;
    bool active = IsObjectRandActive(obj, var_name);
    out = MakeLogic4VecVal(arena, 32, active ? 1 : 0);
    return true;
  }

  // 18.8 / Table 18-3 void form: the argument selects ON (nonzero) or OFF
  // (zero). A named call sets that one variable; a call with no variable name
  // applies to every rand/randc variable in the object's class hierarchy.
  bool on = EvalExpr(expr->args[0], ctx, arena).ToUint64() != 0;
  if (var_name.empty()) {
    SetAllRandVariablesActive(obj, on);
  } else {
    SetObjectRandActive(obj, var_name, on);
  }
  out = MakeLogic4VecVal(arena, 1, 0);
  return true;
}

}  // namespace delta
