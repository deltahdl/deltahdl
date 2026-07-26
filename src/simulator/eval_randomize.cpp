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

namespace {

// 18.3: fold an enum's named-constant list into the concrete integer values it
// defines, applying the same source-order auto-increment rule the type
// declaration uses: a member with an explicit value resets the running counter,
// and each subsequent unspecified member is one greater than the last.
void FoldEnumMemberValues(const std::vector<EnumMember>& members,
                          std::vector<int64_t>& out) {
  int64_t next = 0;
  for (const auto& em : members) {
    if (em.value != nullptr) next = static_cast<int64_t>(em.value->int_val);
    out.push_back(next);
    ++next;
  }
}

// 18.3: for an active random variable of enum type, the solver shall select a
// value only from the set of named constants of that enum, and shall never
// assign a value that lies outside that set even when the value would cast
// cleanly to the enumerated type. Resolve the member's enum type to its named
// constants and record them as the solver domain; a non-enum member is left
// unrestricted. The enum type may be written inline on the declaration
// (`rand enum {...} x;`) or named through a typedef declared on the class or an
// ancestor (`rand col_e x;` as in the 18.3 MyBus example's atype), and a
// package- or module-scope enum typedef is found through the enum registry, so
// all three forms are resolved here.
void PopulateEnumDomain(const ClassMember* m, const ClassTypeInfo* level,
                        SimContext& ctx, RandVariable& var) {
  const DataType& dt = m->data_type;
  if (dt.kind == DataTypeKind::kEnum) {
    FoldEnumMemberValues(dt.enum_members, var.enum_values);
    return;
  }
  if (dt.kind != DataTypeKind::kNamed) return;
  for (const ClassTypeInfo* lvl = level; lvl != nullptr; lvl = lvl->parent) {
    if (lvl->decl == nullptr) continue;
    for (const ClassMember* tm : lvl->decl->members) {
      if (tm->kind == ClassMemberKind::kTypedef &&
          tm->typedef_item != nullptr &&
          tm->typedef_item->typedef_type.kind == DataTypeKind::kEnum &&
          tm->typedef_item->name == dt.type_name) {
        FoldEnumMemberValues(tm->typedef_item->typedef_type.enum_members,
                             var.enum_values);
        return;
      }
    }
  }
  if (const EnumTypeInfo* info = ctx.FindEnumType(dt.type_name)) {
    for (const auto& em : info->members)
      var.enum_values.push_back(static_cast<int64_t>(em.value));
  }
}

// 18.4: build a solver variable for one rand/randc data member. The default
// integral domain is later tightened by the relational constraints.
void AddRandMember(const ClassMember* m, const ClassTypeInfo* level,
                   SimContext& ctx, std::vector<RandInfo>& out) {
  RandInfo info;
  info.name = std::string(m->name);
  info.level = level;
  info.is_static = m->is_static;
  info.var.name = info.name;
  info.var.qualifier =
      m->is_randc ? RandQualifier::kRandc : RandQualifier::kRand;
  uint32_t width = EvalTypeWidth(m->data_type);
  info.var.width = width == 0 ? 32 : width;
  // 18.3: confine an enum-typed random variable to its named-constant set.
  PopulateEnumDomain(m, level, ctx, info.var);
  // 18.4.2: a randc variable's cyclic permutation ranges over every value its
  // declared width admits (0 .. 2**w-1). The generic solver domain defaults to
  // a fixed 16-bit span; leaving a randc on that default would let the cyclic
  // draw range over more values than the member can hold and then truncate on
  // write-back, destroying the no-repeat property over the real declared range.
  // Bind the domain to the declared width here so the permutation matches the
  // range; later constraint folding narrows it further. A plain rand keeps the
  // generic default -- a uniform draw truncated to the member width is still
  // uniform -- so only the cyclic form needs the exact bound.
  if (info.var.qualifier == RandQualifier::kRandc) {
    uint32_t w = info.var.width;
    info.var.min_val = 0;
    info.var.max_val =
        w >= 63 ? INT64_MAX : ((static_cast<int64_t>(1) << w) - 1);
  }
  out.push_back(std::move(info));
}

// 18.5: a comparison of a rand variable against a constant. Fills `out` with
// the typed solver constraint, folds the variable's domain, and returns true;
// other relation shapes return false for the kCustom fallback.
bool TryComparisonConstraint(const Expr* rel, std::vector<RandInfo>& rands,
                             RandomizeCtx& rc, ConstraintExpr& out,
                             bool fold = true) {
  if (!rel || rel->kind != ExprKind::kBinary || !rel->lhs || !rel->rhs)
    return false;
  ConstraintKind kind = ConstraintKind::kEqual;
  if (!ComparisonKind(rel->op, kind)) return false;
  const Expr* var_side = nullptr;
  const Expr* const_side = nullptr;
  bool mirror = false;
  if (rel->lhs->kind == ExprKind::kIdentifier &&
      FindRand(rands, rel->lhs->text)) {
    var_side = rel->lhs;
    const_side = rel->rhs;
  } else if (rel->rhs->kind == ExprKind::kIdentifier &&
             FindRand(rands, rel->rhs->text)) {
    var_side = rel->rhs;
    const_side = rel->lhs;
    mirror = true;
  }
  if (!var_side) return false;
  if (mirror) ComparisonKind(MirrorComparison(rel->op), kind);
  auto c =
      static_cast<int64_t>(EvalExpr(const_side, rc.ctx, rc.arena).ToUint64());
  out.kind = kind;
  out.var_name = std::string(var_side->text);
  out.lo = c;
  out.ref_vars.push_back(out.var_name);
  // 18.5.13: a soft relation must not tighten the variable's draw domain. If it
  // did, a discarded soft preference would still constrain the variable,
  // biasing the result and narrowing the values the hard constraints still
  // allow.
  if (fold)
    if (auto* ri = FindRand(rands, var_side->text)) FoldBound(*ri, kind, c);
  return true;
}

// Evaluate a non-foldable relation against candidate values: bind each rand
// variable as a local so the expression reads the trial value.
bool EvalCustomRelation(const Expr* rel, const std::vector<std::string>& names,
                        RandomizeCtx& rc,
                        const std::unordered_map<std::string, int64_t>& vals) {
  rc.ctx.PushScope();
  rc.ctx.PushThis(rc.obj);
  for (const auto& n : names) {
    auto it = vals.find(n);
    int64_t v = it != vals.end() ? it->second : 0;
    rc.ctx.CreateLocalVariable(n, 32)->value =
        MakeLogic4VecVal(rc.arena, 32, static_cast<uint64_t>(v));
  }
  Logic4Vec r = EvalExpr(rel, rc.ctx, rc.arena);
  rc.ctx.PopThis();
  rc.ctx.PopScope();
  return r.IsTruthy();
}

ConstraintExpr MakeCustomConstraint(const Expr* rel,
                                    const std::vector<RandInfo>& rands,
                                    RandomizeCtx& rc) {
  std::vector<std::string> names;
  names.reserve(rands.size());
  for (const auto& ri : rands) names.push_back(ri.name);
  ConstraintExpr ce;
  ce.kind = ConstraintKind::kCustom;
  ce.ref_vars = names;
  ce.eval_fn = [rel, names,
                &rc](const std::unordered_map<std::string, int64_t>& vals) {
    return EvalCustomRelation(rel, names, rc, vals);
  };
  return ce;
}

// 18.5.10: locate the constraint block named `name` in the object's class
// hierarchy, walking from the dynamic type up to its base classes so the
// most-derived block of a given name wins (matching CollectConstraintBlocks).
// A block qualified 'static' shares one active/inactive state across every
// instance of its declaring class, so its state lives on the ClassTypeInfo
// rather than the object; this returns that declaring type when the block is
// static, and nullptr otherwise.
static const ClassTypeInfo* StaticConstraintOwner(const ClassObject* obj,
                                                  std::string_view name) {
  for (const auto* lvl = obj ? obj->type : nullptr; lvl != nullptr;
       lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kConstraint && m->name == name)
        return m->is_static ? lvl : nullptr;
    }
  }
  return nullptr;
}

}  // namespace

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
  // Named form: the receiver is object.constraint_id.
  if (recv->kind == ExprKind::kMemberAccess && recv->lhs &&
      recv->lhs->kind == ExprKind::kIdentifier && recv->rhs &&
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
                          std::string_view& var_name) {
  if (!expr || expr->kind != ExprKind::kCall) return false;
  const Expr* callee = expr->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return false;
  if (!callee->rhs || callee->rhs->kind != ExprKind::kIdentifier) return false;
  if (callee->rhs->text != "rand_mode") return false;

  const Expr* recv = callee->lhs;
  if (!recv) return false;
  // No-name form: the receiver is the object handle itself.
  if (recv->kind == ExprKind::kIdentifier) {
    obj_name = recv->text;
    var_name = {};
    return true;
  }
  // Named form: the receiver is object.random_variable.
  if (recv->kind == ExprKind::kMemberAccess && recv->lhs &&
      recv->lhs->kind == ExprKind::kIdentifier && recv->rhs &&
      recv->rhs->kind == ExprKind::kIdentifier) {
    obj_name = recv->lhs->text;
    var_name = recv->rhs->text;
    return true;
  }
  return false;
}

// 18.6.1: randomize() sets all of an object's active random variables AND the
// random objects it references to valid values, succeeding only when every one
// is solved. Solve this object's own random variables subject to its active
// constraints and write the results back, then recurse into each non-null rand
// object-handle member so its own random members are randomized as well; the
// overall result fails if any sub-object solve fails. The visited set breaks
// handle cycles so a self- or mutually-referential object graph terminates. A
// null random object handle references nothing to randomize and is skipped.
//
// 18.11: inline_random, when non-null, is the set of property names passed as
// randomize()'s arguments. It names the complete active random set for the
// duration of this one call: a named property is active (and a non-random
// property so named is promoted to a random variable), while every other
// variable becomes a state variable held at its current value. It governs only
// the object named in the call, so it is passed as null on the recursive
// descent into rand sub-objects below.
//
// 18.11.1: null_checker marks the special randomize(null) form, the inline
// constraint checker. It rides on top of the same mechanism: inline_random is
// an empty (but present) set, so every rand/randc variable is excluded from the
// active set and held as a state variable, and no value is drawn for the call.
// Because no class member is randomized, the rand object-handle members are not
// recursed into either -- they too are state variables for this call.
bool RandomizeObject(ClassObject* obj, SimContext& ctx, Arena& arena,
                     const Expr* expr, const ClassMember* inline_block,
                     const std::unordered_set<std::string>* inline_random,
                     bool null_checker,
                     std::unordered_set<const ClassObject*>& visited) {
  if (!obj || !obj->type) return false;
  if (!visited.insert(obj).second) return true;

  // 18.6.3: seed from the object's own RNG so randomize() draws a fresh result
  // each call while staying reproducible from the object's starting state.
  auto seed = static_cast<uint32_t>(ctx.ObjectRng(obj)());
  ConstraintSolver solver(seed);
  RandomizeCtx rc{obj, ctx, arena};

  std::vector<RandInfo> rands;
  CollectRandVariables(obj->type, ctx, rands);
  // 18.11: naming a property in the inline argument list can change the random
  // mode of any class property, even one not declared rand or randc. A named
  // property that is not already among the rand/randc set is looked up and
  // added as an active random variable so it is solved and written back like
  // any other. It is added before the constraint blocks are gathered so a
  // constraint relating to it binds it as a random variable rather than a state
  // constant. The mechanism does not affect the cyclical mode, so the promoted
  // variable is built as a noncyclical rand (AddRandMember keys the qualifier
  // off the member's own randc declaration, which a non-random property does
  // not have).
  if (inline_random != nullptr) {
    for (const auto& nm : *inline_random) {
      if (FindRand(rands, nm) != nullptr) continue;
      const ClassTypeInfo* lvl = nullptr;
      if (const ClassMember* m = FindNamedProperty(obj->type, ctx, nm, &lvl))
        AddRandMember(m, lvl, ctx, rands);
    }
  }
  CollectConstraintBlocks(obj->type, rands, rc, solver);
  // 18.7: the inline constraint block from a randomize() with {...} call is
  // applied along with the object's own constraints -- not in place of them. It
  // is translated into an additional, always-active constraint block using the
  // same machinery as an in-class block, so its relations (and
  // dist/soft/if-else forms) narrow this object's solve exactly like a class
  // constraint. It is applied only to the object named in the call, not to its
  // rand sub-objects, so inline_block is passed as null on the recursive
  // descent below.
  if (inline_block != nullptr) {
    // 18.7: a block preceded by a parenthesized identifier_list is restricted
    // -- only the listed names resolve as the object's random variables; every
    // other name resolves in the calling scope. Translating the block against a
    // rand set filtered to the listed names realizes exactly that: an unlisted
    // name is not found among the rand variables, so it is read from the caller
    // as a constant instead of being treated as one of the object's randoms. An
    // unrestricted block (no parentheses) sees the full rand set.
    if (expr != nullptr && expr->with_has_parens) {
      std::unordered_set<std::string_view> listed(
          expr->with_restrict_ids.begin(), expr->with_restrict_ids.end());
      std::vector<RandInfo> listed_rands;
      for (const auto& ri : rands)
        if (listed.count(ri.name) != 0) listed_rands.push_back(ri);
      AddConstraintMember(inline_block, listed_rands, rc, solver);
    } else {
      AddConstraintMember(inline_block, rands, rc, solver);
    }
  }
  for (auto& ri : rands) {
    if (ri.var.min_val > ri.var.max_val) ri.var.max_val = ri.var.min_val;
    // 18.4.2: a randc variable shall not repeat a value until its permutation
    // is exhausted, and that no-repeat property spans successive randomize()
    // calls. Because the solver is rebuilt for every call, hand it a persistent
    // permutation history to advance in place so the cycle continues across
    // calls instead of restarting each time. A nonstatic randc uses this
    // object's own per-member history; a static randc shares one history held
    // on the (single, per-class) type descriptor, so its cyclic state is static
    // too — a single sequence advances no matter which instance is randomized.
    if (ri.var.qualifier == RandQualifier::kRandc) {
      std::shared_ptr<std::unordered_set<int64_t>>* slot =
          (ri.is_static && ri.level) ? &ri.level->static_randc_history[ri.name]
                                     : &obj->randc_history[ri.name];
      if (!*slot) *slot = std::make_shared<std::unordered_set<int64_t>>();
      ri.var.shared_randc_state = *slot;
    }
    // 18.11: when randomize() is called with an argument list, those arguments
    // designate the complete set of random variables for this call and every
    // other variable is considered a state variable -- conceptually equivalent
    // to rand_mode() calls that enable the named variables and disable the
    // rest. The inline list therefore fully governs the active set here,
    // overriding the persistent rand_mode() state for the duration of the call.
    // Without an argument list (18.8) the persistent per-object rand_mode()
    // flag governs.
    bool active = inline_random != nullptr ? inline_random->count(ri.name) != 0
                                           : IsObjectRandActive(obj, ri.name);
    // 18.8 / 18.11: a variable that is not active is not randomized; the solver
    // treats it as a state variable, holding its current value constant. Seed
    // that value and disable the variable so the solve leaves it untouched
    // while still evaluating any constraint that relates to it.
    if (!active) {
      auto pit = obj->properties.find(ri.name);
      if (pit != obj->properties.end())
        ri.var.value = static_cast<int64_t>(pit->second.ToUint64());
      ri.var.enabled = false;
    }
    solver.AddVariable(ri.var);
  }
  RegisterPreRandomize(obj, expr, ctx, arena, solver);

  bool solved = solver.SolveWith({});
  // 18.6.2: post_randomize() must observe the new values as assigned to the
  // object, so write the solved values back first and only then invoke it. The
  // solver's pre hook already fired before the compute; post is sequenced here,
  // after the writeback, rather than inside the solve.
  if (solved) {
    WriteBackSolved(obj, rands, solver, arena);
    InvokePostRandomize(obj, expr, ctx, arena);
  }

  // 18.11.1: under randomize(null) nothing is randomized, so a rand
  // object-handle member is a state variable and the object it references is
  // left untouched -- do not recurse into it.
  std::vector<std::string> object_members;
  if (!null_checker) CollectRandObjectMembers(obj->type, ctx, object_members);
  for (const auto& name : object_members) {
    // 18.8: rand_mode() on a rand object-handle member changes only that
    // handle's mode. An inactive handle is not one of the object's active
    // random variables, so randomize() does not recurse into the object it
    // references; the referenced object's own variable modes are left as they
    // are (only reached by randomizing that object directly).
    if (!IsObjectRandActive(obj, name)) continue;
    auto it = obj->properties.find(name);
    if (it == obj->properties.end()) continue;
    uint64_t handle = it->second.ToUint64();
    if (handle == kNullClassHandle) continue;
    ClassObject* sub = ctx.GetClassObject(handle);
    if (!sub) continue;
    if (!RandomizeObject(sub, ctx, arena, expr, /*inline_block=*/nullptr,
                         /*inline_random=*/nullptr, /*null_checker=*/false,
                         visited))
      solved = false;
  }
  return solved;
}

// 18.9 / Table 18-4: record a block's active (ON) or inactive (OFF) state for
// this object, as set by a void-form constraint_mode() call.
// 18.5.10: a static block's state is written to the class-wide map, so the
// change takes effect for every instance of the declaring class.
void SetObjectConstraintActive(ClassObject* obj, std::string_view name,
                               bool active) {
  if (const ClassTypeInfo* owner = StaticConstraintOwner(obj, name)) {
    owner->static_constraint_active[std::string(name)] = active;
    return;
  }
  obj->constraint_active[std::string(name)] = active;
}

// 18.8 / Table 18-3: record a random variable's active (ON) or inactive (OFF)
// state for this object, as set by a rand_mode() call.
void SetObjectRandActive(ClassObject* obj, std::string_view name, bool active) {
  obj->rand_active[std::string(name)] = active;
}

// 18.5.3: translate a captured "expression dist { dist_list }" into a kDist
// solver constraint. The distribution names the single variable it weights, so
// the target must be a plain identifier; each item's value/range bounds and its
// weight are constant expressions, folded to integers here. A range keeps its
// per_element flag so the solver spreads a ':=' weight across the range, and an
// item with no explicit weight keeps the DistWeight default weight of 1.
// Returns false for a non-identifier target, leaving the distribution unbuilt.
bool BuildDistConstraint(const ConstraintDistRef& ref, RandomizeCtx& rc,
                         ConstraintExpr& out) {
  if (ref.target == nullptr || ref.target->kind != ExprKind::kIdentifier)
    return false;
  out.kind = ConstraintKind::kDist;
  out.var_name = std::string(ref.target->text);
  for (const auto& item : ref.items) {
    DistWeight w;
    w.is_default = item.is_default;
    w.is_range = item.is_range;
    w.per_element = item.per_element;
    if (item.weight != nullptr)
      w.weight = static_cast<uint32_t>(
          EvalExpr(item.weight, rc.ctx, rc.arena).ToUint64());
    if (item.is_range) {
      w.lo =
          static_cast<int64_t>(EvalExpr(item.lo, rc.ctx, rc.arena).ToUint64());
      w.hi =
          static_cast<int64_t>(EvalExpr(item.hi, rc.ctx, rc.arena).ToUint64());
    } else if (!item.is_default) {
      w.value = static_cast<int64_t>(
          EvalExpr(item.value, rc.ctx, rc.arena).ToUint64());
    }
    out.dist_weights.push_back(w);
  }
  return true;
}

// 18.5.11: gather the identifiers a constraint relation names, partitioned by
// whether the identifier appears in a function-call argument position. 'in_arg'
// is true while descending through the argument subtrees of a call, so a name
// used as (or inside) a function argument is added to 'arg_names' while every
// named identifier is added to 'all_names'. Only the argument subtrees carry
// the in-argument flag; the callee and receiver of a member call do not, so the
// object handle of a qualified call is not mistaken for an argument. The caller
// filters these against the object's random variables.
void CollectConstraintArgRefs(const Expr* e, bool in_arg,
                              std::unordered_set<std::string>& all_names,
                              std::unordered_set<std::string>& arg_names) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier) {
    all_names.insert(std::string(e->text));
    if (in_arg) arg_names.insert(std::string(e->text));
  }
  const bool call = e->kind == ExprKind::kCall;
  CollectConstraintArgRefs(e->lhs, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->rhs, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->condition, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->true_expr, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->false_expr, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->base, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->index, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->index_end, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->with_expr, in_arg, all_names, arg_names);
  CollectConstraintArgRefs(e->repeat_count, in_arg, all_names, arg_names);
  // A call's arguments (and everything nested within them) are in-argument.
  for (const Expr* a : e->args)
    CollectConstraintArgRefs(a, call || in_arg, all_names, arg_names);
  for (const Expr* el : e->elements)
    CollectConstraintArgRefs(el, in_arg, all_names, arg_names);
}

// 18.4: a rand class-handle member names an object; randomize() solves that
// object's own random members and shall never modify the handle itself. The
// handle is therefore not built as a solver variable — doing so would draw an
// integer and overwrite the handle on writeback. (The recursive solve of the
// referenced object is a separate concern; the head-level obligation observed
// here is simply that the handle value is left unchanged.)
bool IsClassHandleMember(const ClassMember* m, SimContext& ctx) {
  return m->data_type.kind == DataTypeKind::kNamed &&
         ctx.FindClassType(m->data_type.type_name) != nullptr;
}

// 18.5: translate one captured constraint relation into a solver
// ConstraintExpr.
ConstraintExpr TranslateRelation(const Expr* rel, std::vector<RandInfo>& rands,
                                 RandomizeCtx& rc, bool fold) {
  ConstraintExpr ce;
  if (TryComparisonConstraint(rel, rands, rc, ce, fold)) return ce;
  return MakeCustomConstraint(rel, rands, rc);
}

void AddConstraintMember(const ClassMember* m, std::vector<RandInfo>& rands,
                         RandomizeCtx& rc, ConstraintSolver& solver) {
  ConstraintBlock block;
  block.name = std::string(m->name);
  block.constraints.reserve(
      m->constraint_exprs.size() + m->constraint_dist_refs.size() +
      m->constraint_soft_exprs.size() + m->constraint_soft_dist_refs.size() +
      m->constraint_disable_soft_refs.size());
  for (const Expr* rel : m->constraint_exprs) {
    block.constraints.push_back(TranslateRelation(rel, rands, rc));
  }
  // 18.5.3: build each captured distribution as a weighted-value constraint.
  for (const auto& ref : m->constraint_dist_refs) {
    ConstraintExpr ce;
    if (BuildDistConstraint(ref, rc, ce)) block.constraints.push_back(ce);
  }
  // 18.5.13.2: build each 'disable soft var' directive as a kDisableSoft solver
  // constraint naming the variable. Emitted before this block's own soft
  // constraints so that, in declaration order, the directive discards only the
  // lower-priority soft constraints already seen (from earlier blocks, or
  // earlier in this block) and never this block's own later soft constraints —
  // matching the class B example where 'disable soft x; soft x dist {5,8};'
  // discards a preceding block's soft but keeps its own following distribution.
  // The solver's ComputeDisabledSoft resolves these against the soft
  // constraints; a directive that names a variable the block does not soft
  // constrain simply discards nothing.
  for (const auto& ref : m->constraint_disable_soft_refs) {
    ConstraintExpr ce;
    ce.kind = ConstraintKind::kDisableSoft;
    ce.var_name = std::string(ref.name);
    block.constraints.push_back(std::move(ce));
  }
  // 18.5.13: build each captured soft constraint. The inner relation is
  // translated exactly like a hard one but without folding the draw domain,
  // then wrapped in a kSoft constraint. The solver seeds the inner so a
  // satisfiable preference is honored, yet discards the soft (treating it as
  // the value 1) and never fails the solve when the preference conflicts with
  // the hard constraints. The inner is heap-owned in rc so the kSoft's raw
  // pointer to it stays valid after the block is copied into the solver.
  for (const Expr* rel : m->constraint_soft_exprs) {
    auto inner = std::make_unique<ConstraintExpr>(
        TranslateRelation(rel, rands, rc, /*fold=*/false));
    ConstraintExpr sc;
    sc.kind = ConstraintKind::kSoft;
    sc.var_name = inner->var_name;
    sc.ref_vars = inner->ref_vars;
    sc.inner = inner.get();
    rc.soft_inners.push_back(std::move(inner));
    block.constraints.push_back(std::move(sc));
  }
  // 18.5.13: a 'soft'-prefixed distribution wraps the dist alternative of the
  // soft operand. Build the inner as an ordinary weighted-value (kDist)
  // constraint, then wrap it in a kSoft: the solver seeds the distribution when
  // it is honored and discards it (leaving its variable free) when it conflicts
  // with the hard constraints.
  for (const auto& ref : m->constraint_soft_dist_refs) {
    auto inner = std::make_unique<ConstraintExpr>();
    if (!BuildDistConstraint(ref, rc, *inner)) continue;
    ConstraintExpr sc;
    sc.kind = ConstraintKind::kSoft;
    sc.var_name = inner->var_name;
    sc.ref_vars.push_back(inner->var_name);
    sc.inner = inner.get();
    rc.soft_inners.push_back(std::move(inner));
    block.constraints.push_back(std::move(sc));
  }
  // 18.5.4: build each captured uniqueness constraint as a kUnique solver
  // constraint. Each range_list member that names an active rand variable is
  // resolved to that solver variable; the solver then requires the named
  // variables to hold pairwise-distinct values, enforces the no-randc and
  // equivalent-type restrictions on the group, and treats a group of fewer than
  // two known members as having no effect. A member the solver does not model
  // as its own variable (e.g. an array slice, whose elements the scalar solver
  // does not draw individually) is left out of the group, mirroring the lenient
  // treatment of unknown references elsewhere in the translation.
  for (const auto& group : m->constraint_unique_refs) {
    ConstraintExpr ce;
    ce.kind = ConstraintKind::kUnique;
    for (const Expr* item : group) {
      if (item != nullptr && item->kind == ExprKind::kIdentifier &&
          FindRand(rands, item->text)) {
        ce.unique_vars.push_back(std::string(item->text));
      }
    }
    ce.ref_vars = ce.unique_vars;
    block.constraints.push_back(std::move(ce));
  }

  // 18.5.9: lower each 'solve before_list before after_list' ordering into the
  // solver's variable ordering. Only a simple local entry that resolves to an
  // active rand variable participates; a qualified reference or an array.size()
  // method — which the scalar solver does not model as its own drawable
  // variable — is left out, mirroring the lenient treatment of unresolved
  // references in the uniqueness lowering above. The ordering only reweights
  // the probability of the legal combinations and never removes a solution, so
  // dropping an unresolved entry merely relaxes the order rather than losing a
  // solution.
  for (const auto& ref : m->constraint_solve_before_refs) {
    std::vector<std::string> before;
    std::vector<std::string> after;
    for (const auto& e : ref.before)
      if (e.is_simple && FindRand(rands, e.name))
        before.push_back(std::string(e.name));
    for (const auto& e : ref.after)
      if (e.is_simple && FindRand(rands, e.name))
        after.push_back(std::string(e.name));
    if (!before.empty() && !after.empty()) solver.AddSolveBefore(before, after);
  }

  // 18.5.11: a random variable used as a function argument in a constraint
  // establishes an implicit priority — it is solved ahead of the variables of
  // the constraint that consumes it, and its committed value is then read as a
  // state variable when the function is called for the lower-priority set. For
  // each hard relation, the rand variables appearing in a function-call
  // argument position outrank the rand variables the relation uses directly, so
  // record that ordering for the solver's priority-layer pass. Only variables
  // the solver models as its own drawable variable participate, mirroring the
  // lenient treatment of unresolved references in the orderings above. A
  // variable used directly is excluded from the lower set of the same relation
  // when it also supplies an argument there, so a self-reference does not
  // fabricate a degenerate cycle; a genuine cycle across relations (each uses
  // the other as an argument) still forms and is rejected by SolveWith.
  for (const Expr* rel : m->constraint_exprs) {
    std::unordered_set<std::string> all_names;
    std::unordered_set<std::string> arg_names;
    CollectConstraintArgRefs(rel, /*in_arg=*/false, all_names, arg_names);
    std::vector<std::string> higher;
    for (const auto& n : arg_names)
      if (FindRand(rands, n)) higher.push_back(n);
    if (higher.empty()) continue;
    std::vector<std::string> lower;
    for (const auto& n : all_names)
      if (arg_names.find(n) == arg_names.end() && FindRand(rands, n))
        lower.push_back(n);
    if (!lower.empty()) solver.AddFunctionArgPriority(higher, lower);
  }

  // 18.9: a block turned inactive by constraint_mode() is not considered by
  // randomize(); it is created active, so an unset block stays enabled.
  block.enabled = IsObjectConstraintActive(rc.obj, m->name);
  solver.AddConstraintBlock(block);
}

// 18.5/18.5.2: build the constraint block(s) from the captured relations of
// every constraint member on the object's class hierarchy. Walking from the
// dynamic type up to its base classes, the first constraint seen for a given
// name is the most-derived one; 18.5.2 says a same-named constraint in a
// derived class replaces the inherited one, so a base constraint of a name
// already contributed by a more-derived level is skipped rather than added
// alongside it. The name is recorded even for an empty (no-effect) derived
// constraint so that it, too, replaces the inherited one.
void CollectConstraintBlocks(const ClassTypeInfo* type,
                             std::vector<RandInfo>& rands, RandomizeCtx& rc,
                             ConstraintSolver& solver) {
  // Walk from the dynamic type up to its base classes so the first constraint
  // seen for a given name is the most-derived one (18.5.2: a same-named derived
  // constraint replaces the inherited one). Buffer the members to build per
  // level rather than adding them as they are seen, so the levels can be added
  // to the solver in a different order than they are scanned.
  std::unordered_set<std::string_view> replaced;
  std::vector<std::vector<const ClassMember*>> per_level;
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    std::vector<const ClassMember*> level_members;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind != ClassMemberKind::kConstraint) continue;
      if (!replaced.insert(m->name).second) continue;
      if (!m->constraint_exprs.empty() || !m->constraint_dist_refs.empty() ||
          !m->constraint_soft_exprs.empty() ||
          !m->constraint_soft_dist_refs.empty() ||
          !m->constraint_unique_refs.empty() ||
          !m->constraint_solve_before_refs.empty() ||
          // 18.5.13.2: a block whose only body is a 'disable soft' directive
          // still contributes — it discards lower-priority soft constraints.
          !m->constraint_disable_soft_refs.empty())
        level_members.push_back(m);
    }
    per_level.push_back(std::move(level_members));
  }
  // 18.5.13.1: constraints in a derived class have higher soft-constraint
  // priority than all constraints in its superclasses. The solver ranks soft
  // priority by the order blocks are added — a block added later outranks an
  // earlier one — so add the levels base class first and the most-derived level
  // last. per_level was filled most-derived first, so walk it in reverse. This
  // reordering is confined to soft-constraint priority: hard constraints must
  // all hold regardless of order, and the ordering/priority edges (18.5.9,
  // 18.5.11) are order-independent sets, so the solutions are unchanged. Within
  // a level the members keep their syntactic declaration order, which fixes
  // their relative priority.
  for (auto it = per_level.rbegin(); it != per_level.rend(); ++it)
    for (const ClassMember* m : *it) AddConstraintMember(m, rands, rc, solver);
}

// 18.11: locate a class property by name for the inline random control list,
// walking the inheritance chain. Unlike CollectRandVariables this ignores the
// rand/randc qualifier, because naming a property in the argument list may make
// even a non-random property one of the object's random variables. Class-handle
// members are excluded so the handle they hold is never overwritten.
const ClassMember* FindNamedProperty(const ClassTypeInfo* type, SimContext& ctx,
                                     std::string_view name,
                                     const ClassTypeInfo** out_level) {
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kProperty &&
          std::string_view(m->name) == name && !IsClassHandleMember(m, ctx)) {
        if (out_level != nullptr) *out_level = lvl;
        return m;
      }
    }
  }
  return nullptr;
}

// 18.11: the property name that a randomize() inline-control argument refers
// to. Such an argument is a plain property reference -- a bare identifier, an
// indexed element, or a member access -- never a computed expression (the
// parser has already rejected those). Returns the referenced name, or an empty
// view for a form that carries none.
std::string_view InlineRandomArgName(const Expr* arg) {
  if (arg == nullptr) return {};
  switch (arg->kind) {
    case ExprKind::kIdentifier:
      return arg->text;
    case ExprKind::kSelect:
      return InlineRandomArgName(arg->base);
    case ExprKind::kMemberAccess:
      return InlineRandomArgName(arg->rhs);
    default:
      return {};
  }
}

// 18.6.2: pre_randomize() is invoked by randomize() before any new random value
// is computed. Register it as the solver's pre hook, which fires ahead of the
// solve. The method is resolved on the object's actual (dynamic) class: because
// randomize() is virtual, an override in the dynamic type is reached even
// through a base-class handle, so pre_randomize() appears to behave virtually.
// A derived class that does not itself declare pre_randomize() resolves to the
// inherited one, which is the effect of automatically invoking
// super.pre_randomize().
void RegisterPreRandomize(ClassObject* obj, const Expr* expr, SimContext& ctx,
                          Arena& arena, ConstraintSolver& solver) {
  const ClassTypeInfo* owner = nullptr;
  if (ModuleItem* pre =
          obj->ResolveMethodForType("pre_randomize", obj->type, &owner)) {
    // Run the body with its defining class as the enclosing scope so an
    // unqualified member resolves to that level (§8.15) and a super call inside
    // an override walks one level up, mirroring an ordinary method dispatch.
    solver.SetPreRandomize([pre, obj, owner, expr, &ctx, &arena] {
      ctx.PushMethodClass(owner);
      ExecInstanceMethodCall(pre, obj, expr, ctx, arena);
      ctx.PopMethodClass();
    });
  }
}

// Resolve the concrete object from the handle. Works equally for a direct class
// handle and an interface-class handle (8.26.9): the dynamic object found from
// the handle is the implementing class instance either way.
ClassObject* ResolveRandomizeTarget(SimContext& ctx,
                                    const MethodCallParts& parts) {
  if (ctx.GetVariableClassType(parts.var_name).empty()) return nullptr;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var) return nullptr;
  uint64_t handle = var->value.ToUint64();
  if (handle == kNullClassHandle) return nullptr;
  ClassObject* obj = ctx.GetClassObject(handle);
  if (!obj || !obj->type) return nullptr;
  return obj;
}

// 18.6.1: write each solved value back to the object, keeping the bare and
// scoped ("Class::name") property aliases in sync so member reads see it.
void WriteBackSolved(ClassObject* obj, std::vector<RandInfo>& rands,
                     ConstraintSolver& solver, Arena& arena) {
  for (auto& ri : rands) {
    if (ri.var.is_real) continue;
    int64_t v = solver.GetValue(ri.name);
    Logic4Vec lv =
        MakeLogic4VecVal(arena, ri.var.width, static_cast<uint64_t>(v));
    // 18.6.3: a static random variable is a single storage shared by every
    // instance of the class, so a successful randomize() must publish the drawn
    // value to that class-wide cell — not to a private per-object copy. Writing
    // it to the instance map would shadow the shared storage for this object
    // and leave the other instances observing the old value, contradicting the
    // rule that each randomize() changes the variable in every class instance.
    // A non-static variable keeps its per-object storage (with the scoped
    // alias).
    if (ri.is_static && ri.level != nullptr) {
      ri.level->static_properties[ri.name] = lv;
    } else {
      obj->properties[ri.name] = lv;
      obj->properties[std::string(ri.level->name) + "::" + ri.name] = lv;
    }
  }
}

TokenKind MirrorComparison(TokenKind op) {
  switch (op) {
    case TokenKind::kGtEq:
      return TokenKind::kLtEq;
    case TokenKind::kLtEq:
      return TokenKind::kGtEq;
    case TokenKind::kGt:
      return TokenKind::kLt;
    case TokenKind::kLt:
      return TokenKind::kGt;
    default:
      return op;  // == and != are symmetric
  }
}

RandInfo* FindRand(std::vector<RandInfo>& rands, std::string_view name) {
  for (auto& ri : rands) {
    if (std::string_view(ri.name) == name) return &ri;
  }
  return nullptr;
}

// 18.4: gather every rand/randc data member visible on the object, walking the
// inheritance chain so inherited random variables are included. Class-handle
// members are skipped so the handle they hold is never overwritten.
void CollectRandVariables(const ClassTypeInfo* type, SimContext& ctx,
                          std::vector<RandInfo>& out) {
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kProperty &&
          (m->is_rand || m->is_randc) && !IsClassHandleMember(m, ctx))
        AddRandMember(m, lvl, ctx, out);
    }
  }
}

// 18.5: the comparison operators a relation can fold into a domain bound or a
// typed solver constraint. Returns the solver kind for the var-on-left form;
// callers mirror the operator for the var-on-right form before calling.
bool ComparisonKind(TokenKind op, ConstraintKind& out) {
  switch (op) {
    case TokenKind::kGtEq:
      out = ConstraintKind::kGreaterEqual;
      return true;
    case TokenKind::kLtEq:
      out = ConstraintKind::kLessEqual;
      return true;
    case TokenKind::kGt:
      out = ConstraintKind::kGreaterThan;
      return true;
    case TokenKind::kLt:
      out = ConstraintKind::kLessThan;
      return true;
    case TokenKind::kEqEq:
      out = ConstraintKind::kEqual;
      return true;
    case TokenKind::kBangEq:
      out = ConstraintKind::kNotEqual;
      return true;
    default:
      return false;
  }
}

// 18.5/18.5.13: tighten a relation 'var <op> constant' into the variable's draw
// domain so the 500-attempt generate-and-test solver reliably hits it.
void FoldBound(RandInfo& ri, ConstraintKind kind, int64_t c) {
  switch (kind) {
    case ConstraintKind::kGreaterEqual:
      ri.var.min_val = std::max(ri.var.min_val, c);
      break;
    case ConstraintKind::kGreaterThan:
      ri.var.min_val = std::max(ri.var.min_val, c + 1);
      break;
    case ConstraintKind::kLessEqual:
      ri.var.max_val = std::min(ri.var.max_val, c);
      break;
    case ConstraintKind::kLessThan:
      ri.var.max_val = std::min(ri.var.max_val, c - 1);
      break;
    default:
      break;
  }
}

// 18.9: report whether a constraint block is active on this object. Every block
// is active when the object is created, so an absent entry means active.
// 18.5.10: for a static block the state is the class-wide one shared by all
// instances, kept on the declaring type rather than on this object.
bool IsObjectConstraintActive(const ClassObject* obj, std::string_view name) {
  if (const ClassTypeInfo* owner = StaticConstraintOwner(obj, name)) {
    auto it = owner->static_constraint_active.find(std::string(name));
    return it == owner->static_constraint_active.end() ? true : it->second;
  }
  auto it = obj->constraint_active.find(std::string(name));
  return it == obj->constraint_active.end() ? true : it->second;
}

}  // namespace delta
