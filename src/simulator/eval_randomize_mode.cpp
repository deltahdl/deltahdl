#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

// 18.9: match a constraint_mode() method call and pull out the object handle
// name and, for the named form obj.constraint_id.constraint_mode(...), the
// constraint block name. The no-name form obj.constraint_mode(...) leaves
// constraint_name empty. Returns false for any other call so normal method
// dispatch proceeds.
bool ExtractConstraintModeParts(const Expr* expr, std::string_view& obj_name,
                                std::string_view& constraint_name) {
  if (!expr || expr->kind != ExprKind::kCall) return false;
  const Expr* callee = expr->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return false;
  if (!callee->rhs || callee->rhs->kind != ExprKind::kIdentifier) return false;
  if (callee->rhs->text != "constraint_mode") return false;

  const Expr* recv = callee->lhs;
  if (!recv) return false;
  // No-name form: the receiver is the object handle itself.
  if (recv->kind == ExprKind::kIdentifier) {
    obj_name = recv->text;
    constraint_name = {};
    return true;
  }
  // Named form: the receiver is object.constraint_id. A scope resolution,
  // `p::h`, is no object's member; ExtractScopedModeParts takes it.
  if (recv->kind == ExprKind::kMemberAccess && !recv->is_scope_resolution &&
      recv->lhs && recv->lhs->kind == ExprKind::kIdentifier && recv->rhs &&
      recv->rhs->kind == ExprKind::kIdentifier) {
    obj_name = recv->lhs->text;
    constraint_name = recv->rhs->text;
    return true;
  }
  return false;
}

// 18.8: match a rand_mode() method call and pull out the object handle name
// and, for the named form obj.random_variable.rand_mode(...), the variable
// name. The no-name form obj.rand_mode(...) leaves var_name empty. Returns
// false for any other call so normal method dispatch proceeds.
bool ExtractRandModeParts(const Expr* expr, std::string_view& obj_name,
                          std::string_view& var_name, const Expr*& element) {
  if (!expr || expr->kind != ExprKind::kCall) return false;
  const Expr* callee = expr->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return false;
  if (!callee->rhs || callee->rhs->kind != ExprKind::kIdentifier) return false;
  if (callee->rhs->text != "rand_mode") return false;

  const Expr* recv = callee->lhs;
  if (!recv) return false;
  element = nullptr;
  // 18.8: the element form, object.array[index].rand_mode(...), names one
  // element of an unpacked array member; the select is handed back for the
  // caller to evaluate its index.
  if (recv->kind == ExprKind::kSelect && recv->index != nullptr &&
      recv->index_end == nullptr && recv->base != nullptr &&
      recv->base->kind == ExprKind::kMemberAccess && recv->base->lhs &&
      recv->base->lhs->kind == ExprKind::kIdentifier && recv->base->rhs &&
      recv->base->rhs->kind == ExprKind::kIdentifier) {
    obj_name = recv->base->lhs->text;
    var_name = recv->base->rhs->text;
    element = recv;
    return true;
  }
  // No-name form: the receiver is the object handle itself.
  if (recv->kind == ExprKind::kIdentifier) {
    obj_name = recv->text;
    var_name = {};
    return true;
  }
  // Named form: the receiver is object.random_variable. A scope resolution,
  // `p::h`, is no object's member; ExtractScopedModeParts takes it.
  if (recv->kind == ExprKind::kMemberAccess && !recv->is_scope_resolution &&
      recv->lhs && recv->lhs->kind == ExprKind::kIdentifier && recv->rhs &&
      recv->rhs->kind == ExprKind::kIdentifier) {
    obj_name = recv->lhs->text;
    var_name = recv->rhs->text;
    return true;
  }
  return false;
}

// §26.3 with §18.8 and §18.9: what a rand_mode() or constraint_mode() call
// through a package-qualified handle names -- the handle's "p.h" key, the
// member named on it or nothing, and for §18.8's element form the select
// whose index the caller evaluates.
struct ScopedModeParts {
  std::string_view obj_name;
  std::string_view name;
  const Expr* element = nullptr;
};

// §26.3 with §18.8 and §18.9: rand_mode() and constraint_mode() through a
// package-qualified handle -- the no-name form `p::h.rand_mode(...)`, whose
// receiver is the scoped handle, the named form `p::h.x.rand_mode(...)`,
// whose receiver is a member access on it, and, for rand_mode alone as
// §18.9 gives constraint_mode no element form, the element form
// `p::h.arr[i].rand_mode(...)`, whose receiver is a single-index select on
// that member access. The two extractors above take an identifier handle
// alone, and read the no-name scoped form as an object p's member h, which
// nothing answered; the element form was refused by every extractor, so the
// call set and read nothing. False for any other call.
static bool ExtractScopedModeParts(const Expr* expr, std::string_view method,
                                   Arena& arena, ScopedModeParts& out) {
  if (!expr || expr->kind != ExprKind::kCall) return false;
  const Expr* callee = expr->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess || !callee->rhs ||
      callee->rhs->kind != ExprKind::kIdentifier ||
      callee->rhs->text != method || !callee->lhs) {
    return false;
  }
  const Expr* recv = callee->lhs;
  out.element = nullptr;
  MethodCallParts parts;
  if (recv->kind == ExprKind::kMemberAccess && recv->is_scope_resolution) {
    if (!ExtractHandleMethodCallParts(expr, arena, parts)) return false;
    out.obj_name = parts.var_name;
    out.name = {};
    return true;
  }
  if (method == "rand_mode" && recv->kind == ExprKind::kSelect &&
      recv->index != nullptr && recv->index_end == nullptr &&
      recv->base != nullptr) {
    out.element = recv;
    recv = recv->base;
  }
  if (recv->kind != ExprKind::kMemberAccess || !recv->lhs ||
      recv->lhs->kind != ExprKind::kMemberAccess ||
      !recv->lhs->is_scope_resolution ||
      !ExtractHandleAccessParts(recv, arena, parts)) {
    return false;
  }
  out.obj_name = parts.var_name;
  out.name = parts.method_name;
  return true;
}

// 18.8: report whether a random variable is active on this object. Every
// rand/randc variable is active when the object is created, so an absent entry
// means active; an explicit entry records the last rand_mode() setting.
const ClassTypeInfo* StaticRandOwner(const ClassObject* obj,
                                     std::string_view name) {
  std::string_view base = name.substr(0, name.find_first_of("[."));
  for (const auto* t = obj->type; t != nullptr; t = t->parent) {
    if (t->decl == nullptr) continue;
    for (const ClassMember* m : t->decl->members) {
      if (m->kind == ClassMemberKind::kProperty && m->name == base)
        return m->is_static ? t : nullptr;
    }
  }
  return nullptr;
}

bool IsObjectRandActive(const ClassObject* obj, std::string_view name) {
  // §18.8: a static variable's state is held by its declaring class.
  const ClassTypeInfo* owner = StaticRandOwner(obj, name);
  const auto& modes =
      owner != nullptr ? owner->static_rand_active : obj->rand_active;
  auto it = modes.find(std::string(name));
  if (it != modes.end()) return it->second;
  // 18.5.7/18.8: an element of a rand member declared as an array, and the
  // size of one declared as a dynamic array, is named by its key, while
  // rand_mode() is called on the member, so each takes the member's state.
  auto bracket = name.find_first_of("[.");
  if (bracket == std::string_view::npos) return true;
  auto base = modes.find(std::string(name.substr(0, bracket)));
  return base == modes.end() ? true : base->second;
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
// Each such member names a sub-object: because randomize() gives a value to
// every random variable and object, every referenced object is randomized in
// turn. Walk the inheritance chain so inherited random object handles are
// included.
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

// The randomize() call `expr` on `obj` under the argument list `args`,
// solved jointly with the object's active random object members where the
// call admits it and on the object alone otherwise; whether it solved.
static bool RandomizeCall(const Expr* expr, ClassObject* obj,
                          const InlineRandomArgs& args, SimContext& ctx,
                          Arena& arena) {
  const std::unordered_set<std::string>& inline_random = args.names;
  bool has_inline_list = args.has_list;
  bool null_checker = args.null_checker;
  std::unordered_set<const ClassObject*> visited;
  // 18.5.8: the plain randomize() form randomizes the object together with all
  // of its active random object members as a single whole, so global
  // constraints relating variables from different objects are solved
  // simultaneously. When the active random object set (rule a) has more than
  // the root object, solve the tree jointly, an inline (with) block applied
  // to the root (18.5.13.1). The argument-list form (18.11), the null
  // checker (18.11.1) and a with clause restricting the variables it names
  // (18.7) keep the per-object path.
  if (!null_checker && !has_inline_list && !expr->with_has_parens) {
    std::vector<JointObject> objects;
    CollectActiveRandomObjects(obj, "", ctx, objects, visited);
    if (objects.size() > 1) {
      return RandomizeObjectTree(ctx, arena, expr, objects,
                                 expr->inline_constraint);
    }
    visited.clear();
  }
  const std::unordered_set<std::string>* active_set =
      (null_checker || has_inline_list) ? &inline_random : nullptr;
  return RandomizeObject(
      obj, ctx, arena,
      {expr, expr->inline_constraint, active_set, null_checker}, visited);
}

namespace {

// 18.11: the arguments of randomize() are properties of the calling object,
// and a local member can be named only where the call has access to it,
// within its class; there the call is written bare, randomize(secret), and
// names the built-in method of the object executing the method, as
// this.randomize(secret) would (8.11).
bool BareRandomizeInMethod(const Expr* expr, SimContext& ctx,
                           MethodCallParts& parts) {
  if (expr->lhs == nullptr || expr->lhs->kind != ExprKind::kIdentifier ||
      expr->lhs->text != "randomize" || ctx.CurrentThis() == nullptr)
    return false;
  parts.var_name = "this";
  parts.method_name = "randomize";
  return true;
}

// The receiver `e` of the call `e.method(...)`, the dot not a package's scope
// resolution; null for an expression of any other shape.
const Expr* ReceiverOfMethod(const Expr* expr, std::string_view method) {
  if (expr->kind != ExprKind::kCall) return nullptr;
  const Expr* callee = expr->lhs;
  if (callee == nullptr || callee->kind != ExprKind::kMemberAccess ||
      callee->is_scope_resolution || callee->lhs == nullptr ||
      callee->rhs == nullptr || callee->rhs->kind != ExprKind::kIdentifier ||
      callee->rhs->text != method) {
    return nullptr;
  }
  return callee->lhs;
}

// 18.6.1 and 18.13 with 8.4: randomize(), srandom(), get_randstate() and
// set_randstate() are methods of the object whatever handle expression yields
// it -- an element of an array of handles, a handle held in another object's
// property, a function's result -- so a receiver that names no handle variable
// is evaluated for the handle it holds. Null when the call is no
// `expr.method(...)` or the handle is null; §8.4 makes the call through a null
// handle illegal, and it is reported here as through a named one.
ClassObject* ExprReceiverObject(const Expr* expr, std::string_view method,
                                SimContext& ctx, Arena& arena) {
  const Expr* recv = ReceiverOfMethod(expr, method);
  if (recv == nullptr) return nullptr;
  uint64_t handle = EvalExpr(recv, ctx, arena).ToUint64();
  if (handle == kNullClassHandle) {
    ReportNullHandleCall(method, expr->lhs->rhs->range.start, ctx);
    return nullptr;
  }
  ClassObject* obj = ctx.GetClassObject(handle);
  return (obj != nullptr && obj->type != nullptr) ? obj : nullptr;
}

// The object a call of the object method `method` runs on: the one a handle
// variable names, resolved by the key ExtractHandleMethodCallParts answers, or
// the one any other receiver expression evaluates to. Null when the call is
// no call of `method` or reaches no object.
ClassObject* ObjectMethodReceiver(const Expr* expr, std::string_view method,
                                  SimContext& ctx, Arena& arena) {
  MethodCallParts parts;
  if (ExtractHandleMethodCallParts(expr, arena, parts)) {
    return parts.method_name == method ? ResolveRandomizeTarget(ctx, parts)
                                       : nullptr;
  }
  return ExprReceiverObject(expr, method, ctx, arena);
}

}  // namespace

// §26.3 admits a package-qualified handle as the receiver of randomize(),
// srandom(), get_randstate() and set_randstate(), `p::h.randomize()`,
// resolved by the key ExtractHandleMethodCallParts answers; taken as an
// identifier alone, the scoped call resolved no object and drew nothing.
bool TryEvalRandomizeMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  MethodCallParts parts;
  ClassObject* obj = BareRandomizeInMethod(expr, ctx, parts)
                         ? ResolveRandomizeTarget(ctx, parts)
                         : ObjectMethodReceiver(expr, "randomize", ctx, arena);
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
  // 18.7: the members of the caller's own object that the inline block
  // names are bound as locals for the call, in a scope of their own.
  ctx.PushScope();
  BindCallersMembers(expr, obj, ctx, arena);
  BindCallersVariables(expr, obj, ctx, arena);
  bool solved = RandomizeCall(expr, obj, args, ctx, arena);
  ctx.PopScope();
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

// 18.12: whether every expression of a scope randomize's constraint_block
// is true on the current values of the scope's variables, the check the
// call with no argument makes in place of a draw.
uint64_t ScopeConstraintsHold(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->inline_constraint == nullptr) return 1;
  for (const Expr* rel : expr->inline_constraint->constraint_exprs) {
    if (EvalExpr(rel, ctx, arena).ToUint64() == 0) return 0;
  }
  return 1;
}

}  // namespace

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
    // 6.11.3: the variable's declared signedness fixes which half of the
    // w-bit range the domain covers, so a signed scope variable can be drawn
    // negative and a constraint requiring a negative value is satisfiable.
    ri.var.is_signed = targets[i]->is_signed;
    ri.var.BindDomainToDeclaredRange();
    ri.var.value = ri.var.ValueFromBits(targets[i]->value.ToUint64());
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
    // The target's declared signedness lives on the variable, not on the value
    // held in it, and a read derives the value's signedness from there, so
    // storing the drawn bits leaves a negative draw reading back negative.
    targets[i]->value = MakeLogic4VecVal(
        arena, w, static_cast<uint64_t>(solver.GetValue(names[i])));
  }
}

// 18.12: the variables a scope randomize call names, each with its name; and,
// 18.12 with §8.6, each stand-in for a property of the object a method runs
// on, named bare, with the property the value drawn for it is written back
// to.
struct ScopeTargets {
  std::vector<Variable*> vars;
  std::vector<std::string> names;
  std::vector<std::pair<Variable*, FieldTarget>> properties;
};

// 18.12: the variables the arguments of the scope randomize call `expr` name,
// into `out`; false where an argument is no identifier naming one. A property
// named bare is a variable visible in the method's scope, solved through a
// stand-in holding its value.
static bool ResolveScopeTargets(const Expr* expr, SimContext& ctx, Arena& arena,
                                ScopeTargets& out) {
  for (const Expr* arg : expr->args) {
    if (arg == nullptr || arg->kind != ExprKind::kIdentifier) return false;
    Variable* var = ctx.FindVariable(arg->text);
    if (var == nullptr) {
      FieldTarget field = ResolveBarePropertyTarget(arg->text, ctx);
      if (!field.HasDeposit()) return false;
      var = arena.Create<Variable>();
      var->value = EvalExpr(arg, ctx, arena);
      var->is_signed = var->value.is_signed;
      out.properties.emplace_back(var, field);
    }
    out.vars.push_back(var);
    out.names.emplace_back(arg->text);
  }
  return true;
}

bool TryEvalScopeRandomizeCall(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  if (!IsScopeRandomizeForm(expr, ctx)) return false;

  // 18.12: the arguments specify the variables of the current scope that are to
  // be assigned random values. Resolve each to a live scope variable; a
  // non-identifier argument is not a form this scope randomize path services,
  // so defer to ordinary dispatch rather than misfire.
  ScopeTargets scope;
  if (!ResolveScopeTargets(expr, ctx, arena, scope)) return false;
  std::vector<Variable*>& targets = scope.vars;
  std::vector<std::string>& names = scope.names;

  // 18.12: called with no argument, the scope randomize does not change the
  // value of any variable and instead checks its constraints: every
  // expression of its constraint_block is evaluated, and the call returns 0
  // where one of them is false and 1 otherwise, so without a block (the
  // 18.12.1 form) there is nothing to be false and it returns 1.
  if (targets.empty()) {
    out = MakeLogic4VecVal(arena, 32, ScopeConstraintsHold(expr, ctx, arena));
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
  rc.solver = &solver;
  std::vector<ConstraintExpr> with_constraints =
      TranslateScopeWithBlock(expr, rands, rc);

  for (auto& ri : rands) {
    // A with-block bound may have folded the domain past its own limit (e.g.
    // two opposing bounds); keep it well-formed before handing it to the
    // solver.
    ri.var.CollapseEmptyDomain();
    solver.AddVariable(ri.var);
  }

  bool ok = solver.SolveWith(with_constraints);

  // 18.12: the call returns 1 only when it successfully sets all the random
  // variables to valid values, in which case each drawn value is written back;
  // otherwise it returns 0. 18.6.3: on failure the variables retain their
  // previous values, so nothing is written back.
  if (ok) {
    WriteBackScopeSolved(targets, names, solver, arena);
    for (const auto& [stand_in, field] : scope.properties)
      WriteResolvedField(field, stand_in->value, ctx, arena);
  }
  out = MakeLogic4VecVal(arena, 32, ok ? 1 : 0);
  return true;
}

bool TryEvalObjectSrandom(const Expr* expr, SimContext& ctx, Arena& arena,
                          Logic4Vec& out) {
  ClassObject* obj = ObjectMethodReceiver(expr, "srandom", ctx, arena);
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
  ClassObject* obj = ObjectMethodReceiver(expr, "get_randstate", ctx, arena);
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
  ClassObject* obj = ObjectMethodReceiver(expr, "set_randstate", ctx, arena);
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

namespace {

// §18.8 and §18.9: the object a rand_mode() or constraint_mode() call acts on,
// null where its receiver yields none; the random variable or constraint block
// the call names, empty for the call on the object as a whole; and for §18.8's
// element form the select whose index the caller evaluates.
struct ModeTarget {
  ClassObject* obj = nullptr;
  std::string_view name;
  const Expr* element = nullptr;
};

// Whether the class declaration `decl` declares `name` as a constraint block,
// for `block`, or else as a random variable, rand or randc.
bool DeclaresModeMemberIn(const ClassDecl* decl, std::string_view name,
                          bool block) {
  for (const ClassMember* m : decl->members) {
    if (m->name != name) continue;
    if (block ? m->kind == ClassMemberKind::kConstraint
              : m->kind == ClassMemberKind::kProperty &&
                    (m->is_rand || m->is_randc)) {
      return true;
    }
  }
  return false;
}

// Whether the object's class, or a class it extends, declares `name` as what
// the call `method` controls: a random variable for rand_mode() (§18.8), a
// constraint block for constraint_mode() (§18.9). A built-in class declares
// neither.
bool DeclaresModeMember(const ClassObject* obj, std::string_view name,
                        std::string_view method) {
  bool block = method == "constraint_mode";
  for (const auto* lvl = obj->type; lvl != nullptr; lvl = lvl->parent) {
    if (lvl->decl != nullptr && DeclaresModeMemberIn(lvl->decl, name, block))
      return true;
  }
  return false;
}

// The object the handle `value` refers to, null for a null handle. §8.4 makes
// a call through a null handle illegal, so the call `call` is reported.
ClassObject* ModeObject(const Logic4Vec& value, const Expr* call,
                        SimContext& ctx) {
  uint64_t handle = value.ToUint64();
  if (handle == kNullClassHandle) {
    ReportNullHandleCall(call->lhs->rhs->text, call->lhs->rhs->range.start,
                         ctx);
  }
  return ctx.GetClassObject(handle);
}

// §8.6 with §18.8 and §18.9: a receiver no name resolves -- a call's result,
// `pk().x.rand_mode(0)`, an element of an array of handles,
// `ks[1].x.rand_mode(0)`, or a handle another object holds -- reaches its
// object by its value, evaluated once (§11.3.1). The receiver `e.m`, or for
// rand_mode()'s element form `e.m[i]`, names the member m of e's object where
// that object declares m as what the method controls; otherwise the receiver
// is itself the handle the call is made on, read with e held so that e is not
// evaluated again. False when the call is no call of `method`; `out.obj` is
// null where the receiver yields no object.
bool ResolveExprModeTarget(const Expr* expr, std::string_view method,
                           SimContext& ctx, Arena& arena, ModeTarget& out) {
  const Expr* recv = ReceiverOfMethod(expr, method);
  if (recv == nullptr) return false;
  const Expr* member = recv;
  if (method == "rand_mode" && recv->kind == ExprKind::kSelect &&
      recv->index != nullptr && recv->index_end == nullptr &&
      recv->base != nullptr) {
    member = recv->base;
  }
  if (member->kind != ExprKind::kMemberAccess || member->is_scope_resolution ||
      member->lhs == nullptr || member->rhs == nullptr ||
      member->rhs->kind != ExprKind::kIdentifier) {
    out.obj = ModeObject(EvalExpr(recv, ctx, arena), expr, ctx);
    return true;
  }
  Logic4Vec owner_value = EvalExpr(member->lhs, ctx, arena);
  ClassObject* owner = ModeObject(owner_value, expr, ctx);
  if (owner == nullptr) return true;
  if (DeclaresModeMember(owner, member->rhs->text, method)) {
    out = {owner, member->rhs->text, member == recv ? nullptr : recv};
    return true;
  }
  ctx.SetDeferredArgSnapshot(member->lhs, owner_value);
  out.obj = ModeObject(EvalExpr(recv, ctx, arena), expr, ctx);
  ctx.ClearDeferredArgSnapshot(member->lhs);
  return true;
}

// The target of a rand_mode() or constraint_mode() call: through a handle's
// name, `h.x.rand_mode(0)` or `p::h.x.rand_mode(0)`, the object the name holds,
// and through any other receiver the object its value refers to
// (ResolveExprModeTarget). False when the call is no call of `method`, or
// its name holds no object.
bool ResolveModeTarget(const Expr* expr, std::string_view method,
                       SimContext& ctx, Arena& arena, ModeTarget& out) {
  std::string_view obj_name;
  bool named = method == "rand_mode"
                   ? ExtractRandModeParts(expr, obj_name, out.name, out.element)
                   : ExtractConstraintModeParts(expr, obj_name, out.name);
  if (!named) {
    ScopedModeParts scoped;
    if (!ExtractScopedModeParts(expr, method, arena, scoped)) {
      return ResolveExprModeTarget(expr, method, ctx, arena, out);
    }
    obj_name = scoped.obj_name;
    out.name = scoped.name;
    out.element = scoped.element;
  }
  MethodCallParts parts;
  parts.var_name = obj_name;
  out.obj = ResolveRandomizeTarget(ctx, parts);
  return out.obj != nullptr;
}

// The value of a mode call that reaches no object, which acts on nothing: the
// nonvoid form's int or the void form's bit.
Logic4Vec NullTargetResult(const Expr* expr, Arena& arena) {
  return MakeLogic4VecVal(arena, expr->args.empty() ? 32 : 1, 0);
}

}  // namespace

bool IsModeMethodCall(const Expr* expr) {
  return ReceiverOfMethod(expr, "rand_mode") != nullptr ||
         ReceiverOfMethod(expr, "constraint_mode") != nullptr;
}

bool TryEvalObjectConstraintMode(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  ModeTarget target;
  if (!ResolveModeTarget(expr, "constraint_mode", ctx, arena, target)) {
    return false;
  }
  ClassObject* obj = target.obj;
  if (obj == nullptr) {
    out = NullTargetResult(expr, arena);
    return true;
  }
  std::string_view constraint_name = target.name;

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
  ModeTarget target;
  if (!ResolveModeTarget(expr, "rand_mode", ctx, arena, target)) return false;
  ClassObject* obj = target.obj;
  if (obj == nullptr) {
    out = NullTargetResult(expr, arena);
    return true;
  }
  std::string_view var_name = target.name;
  const Expr* element = target.element;
  // 18.8: an element of an unpacked array member is named by its key, the
  // one the solver's variable for it carries.
  std::string element_key;
  if (element != nullptr) {
    auto index =
        static_cast<int64_t>(EvalExpr(element->index, ctx, arena).ToUint64());
    element_key = ClassArrayElementKey(var_name, index);
    var_name = element_key;
  }

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
