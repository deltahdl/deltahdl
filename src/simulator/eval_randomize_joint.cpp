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

// 18.5.8 rule a: determine the set of objects to be randomized as a whole.
// Starting from the object that invoked randomize(), add every object it
// contains through a rand class-handle member that is itself active (18.8) and
// non-null; recurse so the definition reaches the whole tree of active random
// objects. The visited set breaks handle cycles so a self- or mutually
// referential graph terminates.
void CollectActiveRandomObjects(
    ClassObject* obj, const std::string& prefix, SimContext& ctx,
    std::vector<JointObject>& out,
    std::unordered_set<const ClassObject*>& visited) {
  if (!obj || !obj->type) return;
  if (!visited.insert(obj).second) return;
  out.push_back({obj, prefix});

  std::vector<std::string> handles;
  CollectRandObjectMembers(obj->type, ctx, handles);
  for (const auto& name : handles) {
    // 18.8: an inactive rand handle is not one of the object's active random
    // variables, so the object it references is not part of the active set.
    if (!IsObjectRandActive(obj, name)) continue;
    auto it = obj->properties.find(name);
    if (it == obj->properties.end()) continue;
    uint64_t handle = it->second.ToUint64();
    if (handle == kNullClassHandle) continue;
    ClassObject* sub = ctx.GetClassObject(handle);
    if (!sub) continue;
    CollectActiveRandomObjects(sub, prefix + name + ".", ctx, out, visited);
  }
}

// 18.5.8 rule c: gather the active random variables of every object in the tree
// into one joint table. Each object's own rand/randc data members are given a
// path-qualified solver name so members that share a plain name on different
// objects never collide. The solver domain matters here for a reason of its
// own: a value drawn to satisfy a custom global constraint is checked at full
// width, so a domain wider than the member turns the write-back truncation into
// the difference between a satisfying and a violating assignment. Renaming a
// collected variable does not change the type it was declared with, so the
// domain CollectRandVariables bound from that type carries over untouched --
// re-deriving it here would only be a second copy of the same rule, free to
// drift from the one the standard states.
void CollectJointRandVariables(const std::vector<JointObject>& objects,
                               SimContext& ctx, std::vector<RandInfo>& out) {
  for (const auto& jo : objects) {
    std::vector<RandInfo> local;
    CollectRandVariables(jo.obj->type, ctx, local);
    for (auto& ri : local) {
      ri.member = ri.name;
      ri.owner = jo.obj;
      ri.name = jo.prefix + ri.name;
      ri.var.name = ri.name;
      out.push_back(std::move(ri));
    }
  }
}

// 18.5.8: resolve a constraint operand to the path-qualified name of a joint
// rand variable, or an empty string when the operand is not one (so it is a
// state variable, whose current value is a constant). A bare identifier names a
// rand member of the constraint's own object -- prefix + id. A one-level
// handle.field member access names a rand member of a nested object reached
// through the owner's rand handle -- prefix + handle + "." + field. Only names
// present in the joint set qualify; everything else is a constant.
std::string ResolveJointOperand(const Expr* e, const std::string& prefix,
                                const std::unordered_set<std::string>& names) {
  if (e == nullptr) return {};
  if (e->kind == ExprKind::kIdentifier) {
    std::string q = prefix + std::string(e->text);
    return names.count(q) != 0 ? q : std::string{};
  }
  if (e->kind == ExprKind::kMemberAccess && e->lhs != nullptr &&
      e->lhs->kind == ExprKind::kIdentifier && e->rhs != nullptr &&
      e->rhs->kind == ExprKind::kIdentifier) {
    std::string q =
        prefix + std::string(e->lhs->text) + "." + std::string(e->rhs->text);
    return names.count(q) != 0 ? q : std::string{};
  }
  return {};
}

// 18.5.8: true when an expression references any joint rand variable, so it is
// not a solve-time constant. A member access is resolved as a whole -- its
// field identifier is never treated as a bare-identifier operand, so a nested
// `.v` is not confused with a same-named variable of the constraint's own
// object.
bool RefsJointVar(const Expr* e, const std::string& prefix,
                  const std::unordered_set<std::string>& names) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kMemberAccess)
    return !ResolveJointOperand(e, prefix, names).empty();
  if (RefsJointVar(e->lhs, prefix, names)) return true;
  if (RefsJointVar(e->rhs, prefix, names)) return true;
  if (RefsJointVar(e->base, prefix, names)) return true;
  for (const Expr* a : e->args)
    if (RefsJointVar(a, prefix, names)) return true;
  return false;
}

// 18.5.8: collect the qualified names of the joint variables an expression
// references (for the priority/ordered passes; the flat pass checks every
// constraint regardless). A member access is taken atomically so its field is
// not walked as a separate identifier.
void CollectJointRefs(const Expr* e, const std::string& prefix,
                      const std::unordered_set<std::string>& names,
                      std::vector<std::string>& out) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kMemberAccess) {
    std::string q = ResolveJointOperand(e, prefix, names);
    if (!q.empty()) out.push_back(q);
    return;
  }
  CollectJointRefs(e->lhs, prefix, names, out);
  CollectJointRefs(e->rhs, prefix, names, out);
  CollectJointRefs(e->base, prefix, names, out);
  for (const Expr* a : e->args) CollectJointRefs(a, prefix, names, out);
}

// 18.5.8: build a custom joint constraint. A global constraint relates random
// variables from different objects, so it cannot fold one side into a domain
// bound; instead it is checked against trial values. On each evaluation the
// trial value of every joint variable is written into its owning object's
// property, the relation is evaluated in the owner's scope so a member access
// like left.v reads the trial value from the referenced object, and the
// original property values are restored. This lets the solver see every
// referenced variable at its trial value simultaneously, which is what "solved
// simultaneously" requires.
//
// One property value replaced for the duration of a trial evaluation, together
// with the value it held before (or the fact that it held none).
struct SavedJointProperty {
  ClassObject* obj;
  std::string key;
  bool had;
  Logic4Vec old;
};

// Write each solver trial value onto the object that owns it, remembering what
// was there so the object graph can be restored afterwards. A member is written
// under both its bare name and its class-qualified alias, exactly as a solved
// value is written back.
std::vector<SavedJointProperty> ApplyJointTrialValues(
    std::vector<RandInfo>& rands,
    const std::unordered_map<std::string, int64_t>& vals, Arena& arena) {
  std::vector<SavedJointProperty> saved;
  auto stash = [&saved](ClassObject* o, const std::string& key,
                        const Logic4Vec& nv) {
    auto pit = o->properties.find(key);
    saved.push_back({o, key, pit != o->properties.end(),
                     pit != o->properties.end() ? pit->second : Logic4Vec{}});
    o->properties[key] = nv;
  };
  for (auto& ri : rands) {
    auto vit = vals.find(ri.name);
    if (vit == vals.end()) continue;
    Logic4Vec nv = MakeLogic4VecVal(arena, ri.var.width,
                                    static_cast<uint64_t>(vit->second));
    nv.is_signed = ri.var.is_signed;
    stash(ri.owner, ri.member, nv);
    if (ri.level != nullptr)
      stash(ri.owner, std::string(ri.level->name) + "::" + ri.member, nv);
  }
  return saved;
}

// Undo the trial write, restoring each property to the value it held (or
// removing it again when it held none). Applied in reverse so a key written
// twice ends at its original value.
void RestoreJointProperties(const std::vector<SavedJointProperty>& saved) {
  for (auto it = saved.rbegin(); it != saved.rend(); ++it) {
    if (it->had)
      it->obj->properties[it->key] = it->old;
    else
      it->obj->properties.erase(it->key);
  }
}

ConstraintExpr MakeJointCustomConstraint(const Expr* rel,
                                         const JointVarScope& scope,
                                         RandomizeCtx& rc) {
  ConstraintExpr ce;
  ce.kind = ConstraintKind::kCustom;
  CollectJointRefs(rel, scope.prefix, scope.names, ce.ref_vars);
  std::vector<RandInfo>* jr = &scope.rands;
  ClassObject* owner = scope.owner;
  ce.eval_fn = [rel, owner, jr,
                &rc](const std::unordered_map<std::string, int64_t>& vals) {
    auto saved = ApplyJointTrialValues(*jr, vals, rc.arena);
    rc.ctx.PushScope();
    bool truthy = false;
    {
      ConstraintEvalScope scope(owner, rc.ctx);
      truthy = EvalExpr(rel, rc.ctx, rc.arena).IsTruthy();
    }
    rc.ctx.PopScope();
    RestoreJointProperties(saved);
    return truthy;
  };
  return ce;
}

// A comparison whose other side is a genuine constant (no joint variable) keeps
// the folding/seeding fast path -- qualified to the owner's path and evaluated
// in the owner's scope -- so an equality or bound is still hit reliably; this
// is also how a global constraint against a state variable (rule c) is handled,
// its held value folded in as the constant. False means the relation ties two
// joint variables together, or is not a plain comparison.
bool TryJointComparison(const Expr* rel, const JointVarScope& scope,
                        RandomizeCtx& rc, ConstraintExpr& out) {
  if (rel == nullptr || rel->kind != ExprKind::kBinary || rel->lhs == nullptr ||
      rel->rhs == nullptr)
    return false;
  ConstraintKind kind = ConstraintKind::kEqual;
  if (!ComparisonKind(rel->op, kind)) return false;
  std::string lname = ResolveJointOperand(rel->lhs, scope.prefix, scope.names);
  std::string rname = ResolveJointOperand(rel->rhs, scope.prefix, scope.names);
  std::string vname;
  const Expr* const_side = nullptr;
  bool mirror = false;
  if (!lname.empty() && !RefsJointVar(rel->rhs, scope.prefix, scope.names)) {
    vname = lname;
    const_side = rel->rhs;
  } else if (!rname.empty() &&
             !RefsJointVar(rel->lhs, scope.prefix, scope.names)) {
    vname = rname;
    const_side = rel->lhs;
    mirror = true;
  }
  if (vname.empty()) return false;
  if (mirror) ComparisonKind(MirrorComparison(rel->op), kind);
  rc.ctx.PushScope();
  int64_t c = 0;
  {
    ConstraintEvalScope eval_scope(scope.owner, rc.ctx);
    c = static_cast<int64_t>(EvalExpr(const_side, rc.ctx, rc.arena).ToUint64());
  }
  rc.ctx.PopScope();
  out.kind = kind;
  out.var_name = vname;
  out.lo = c;
  out.ref_vars.push_back(vname);
  if (RandInfo* ri = FindRand(scope.rands, vname)) FoldBound(*ri, kind, c);
  return true;
}

// 18.5.8: translate one relation of an object's constraint for the joint solve.
// Any relation the comparison fast path above does not take becomes a custom
// joint constraint checked against trial values.
ConstraintExpr BuildJointRelation(const Expr* rel, const JointVarScope& scope,
                                  RandomizeCtx& rc) {
  ConstraintExpr out;
  if (TryJointComparison(rel, scope, rc, out)) return out;
  return MakeJointCustomConstraint(rel, scope, rc);
}

// 18.5.8 rule b: select the active constraints of every object in the tree.
// Each object's constraint blocks are collected the same way as for a single
// object (a same-named derived block replaces an inherited one) and translated
// into the shared solver. Only relational constraint expressions are carried
// through the joint path; the tree cases that arise relate simple relational
// and equality constraints, so dist/soft/foreach constraints on a nested object
// are left to the per-object path and not reached here.
// One constraint member of one class level, translated into a solver block.
void AddJointConstraintBlock(const ClassMember* m, const JointObject& jo,
                             const JointVarScope& scope, RandomizeCtx& rc,
                             ConstraintSolver& solver) {
  ConstraintBlock block;
  block.name = std::string(m->name);
  for (const Expr* rel : m->constraint_exprs)
    block.constraints.push_back(BuildJointRelation(rel, scope, rc));
  // 18.9: a block turned off by constraint_mode() is not considered.
  block.enabled = IsObjectConstraintActive(jo.obj, m->name);
  solver.AddConstraintBlock(block);
}

void CollectJointConstraints(const JointObject& jo,
                             std::vector<RandInfo>& rands,
                             const std::unordered_set<std::string>& names,
                             RandomizeCtx& rc, ConstraintSolver& solver) {
  const JointVarScope kScope{jo.obj, jo.prefix, rands, names};
  std::unordered_set<std::string_view> replaced;
  for (const auto* lvl = jo.obj->type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind != ClassMemberKind::kConstraint) continue;
      if (!replaced.insert(m->name).second) continue;
      if (m->constraint_exprs.empty()) continue;
      AddJointConstraintBlock(m, jo, kScope, rc, solver);
    }
  }
}

// 18.5.8: randomize the whole active random object tree as one problem. A
// single solver holds every active random variable (rule c) and every active
// constraint (rule b) of every active random object (rule a), so global
// constraints that relate variables from different objects are solved
// simultaneously. The result is written back to each object, and 18.6.2's
// pre/post_randomize() fire on the object and on each of its random object
// members.
// 18.4.2: continue a randc member's cyclic permutation across calls through its
// persistent history, per object (or per class for a static randc).
void BindJointRandcHistory(RandInfo& ri) {
  if (ri.var.qualifier != RandQualifier::kRandc) return;
  std::shared_ptr<std::unordered_set<int64_t>>* slot =
      (ri.is_static && ri.level) ? &ri.level->static_randc_history[ri.member]
                                 : &ri.owner->randc_history[ri.member];
  if (!*slot) *slot = std::make_shared<std::unordered_set<int64_t>>();
  ri.var.shared_randc_state = *slot;
}

// Hand each joint random variable to the solver. 18.8 / 18.5.8 rule c: a
// variable made inactive by rand_mode() is not randomized; it holds its current
// value as a state constant that a global constraint solved alongside it sees
// as a fixed operand.
void PrepareJointRandVariables(std::vector<RandInfo>& rands,
                               ConstraintSolver& solver) {
  for (auto& ri : rands) {
    ri.var.CollapseEmptyDomain();
    BindJointRandcHistory(ri);
    if (!IsObjectRandActive(ri.owner, ri.member)) {
      auto pit = ri.owner->properties.find(ri.member);
      if (pit != ri.owner->properties.end())
        ri.var.value = static_cast<int64_t>(pit->second.ToUint64());
      ri.var.enabled = false;
    }
    solver.AddVariable(ri.var);
  }
}

// 18.6.2: pre_randomize() runs on the object and on all of its random object
// members before any new value is computed. Each is resolved on its dynamic
// class so an override is reached and an absent one inherits the base method.
void RegisterJointPreRandomize(const std::vector<JointObject>& objects,
                               const Expr* expr, SimContext& ctx, Arena& arena,
                               ConstraintSolver& solver) {
  solver.SetPreRandomize([&objects, expr, &ctx, &arena] {
    for (const auto& jo : objects) {
      const ClassTypeInfo* owner = nullptr;
      if (ModuleItem* pre = jo.obj->ResolveMethodForType(
              "pre_randomize", jo.obj->type, &owner)) {
        ctx.PushMethodClass(owner);
        ExecInstanceMethodCall(pre, jo.obj, expr, ctx, arena);
        ctx.PopMethodClass();
      }
    }
  });
}

// Write each solved value back to the object that owns the variable. 18.6.3: as
// in the single-object path, a static random variable's drawn value belongs in
// the class-wide shared cell so every instance observes it; a per-object write
// would shadow that shared storage.
void WriteBackJointSolved(std::vector<RandInfo>& rands,
                          const ConstraintSolver& solver, Arena& arena) {
  for (auto& ri : rands) {
    if (ri.var.is_real) continue;
    int64_t v = solver.GetValue(ri.name);
    Logic4Vec lv =
        MakeLogic4VecVal(arena, ri.var.width, static_cast<uint64_t>(v));
    // 6.11.3: the member's declared signedness belongs to the value stored in
    // it, so a negative draw reads back as that negative number.
    lv.is_signed = ri.var.is_signed;
    if (ri.is_static && ri.level != nullptr) {
      ri.level->static_properties[ri.member] = lv;
      continue;
    }
    ri.owner->properties[ri.member] = lv;
    if (ri.level != nullptr)
      ri.owner->properties[std::string(ri.level->name) + "::" + ri.member] = lv;
  }
}

bool RandomizeObjectTree(SimContext& ctx, Arena& arena, const Expr* expr,
                         const std::vector<JointObject>& objects) {
  ClassObject* root = objects.front().obj;
  auto seed = static_cast<uint32_t>(ctx.ObjectRng(root)());
  ConstraintSolver solver(seed);
  RandomizeCtx rc{root, ctx, arena};

  std::vector<RandInfo> rands;
  CollectJointRandVariables(objects, ctx, rands);
  std::unordered_set<std::string> names;
  for (const auto& ri : rands) names.insert(ri.name);

  for (const auto& jo : objects)
    CollectJointConstraints(jo, rands, names, rc, solver);

  PrepareJointRandVariables(rands, solver);
  RegisterJointPreRandomize(objects, expr, ctx, arena, solver);

  bool solved = solver.SolveWith({});
  if (solved) {
    WriteBackJointSolved(rands, solver, arena);
    // 18.6.2: post_randomize() runs after the new values are written back, so
    // each object's post_randomize() reads its members at their solved values.
    for (const auto& jo : objects)
      InvokePostRandomize(jo.obj, expr, ctx, arena);
  }
  return solved;
}

}  // namespace delta
