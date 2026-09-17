#include <algorithm>
#include <cstdint>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
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

// The value of `e` with the trial values written onto the objects that own
// them, evaluated in the owner's scope, read as the type it takes.
Logic4Vec EvalJointTrial(const Expr* e, ClassObject* owner,
                         std::vector<RandInfo>& jr, RandomizeCtx& rc,
                         const std::unordered_map<std::string, int64_t>& vals) {
  auto saved = ApplyJointTrialValues(jr, vals, rc.arena);
  rc.ctx.PushScope();
  Logic4Vec value;
  {
    ConstraintEvalScope scope(owner, rc.ctx);
    value = EvalExpr(e, rc.ctx, rc.arena);
  }
  rc.ctx.PopScope();
  RestoreJointProperties(saved);
  return value;
}

// 18.5.8: the side of the comparison `rel` that is a joint variable, bare
// or as handle.field, the other side does not reference, so that the other
// side derives it, the clause's left.v <= v deriving left.v, filling `cmp`
// with the comparison as read from that side and `name` with the variable;
// nullptr where neither side is, or the relation is no comparison, or an
// inequality, which bounds nothing.
const Expr* DerivedJointSide(const Expr* rel, const JointVarScope& scope,
                             ConstraintKind& cmp, std::string& name) {
  if (rel->kind != ExprKind::kBinary || rel->lhs == nullptr ||
      rel->rhs == nullptr || rel->op == TokenKind::kBangEq ||
      !ComparisonKind(rel->op, cmp)) {
    return nullptr;
  }
  for (const Expr* side : {rel->lhs, rel->rhs}) {
    const Expr* other = side == rel->lhs ? rel->rhs : rel->lhs;
    std::string q = ResolveJointOperand(side, scope.prefix, scope.names);
    if (q.empty()) continue;
    std::vector<std::string> refs;
    CollectJointRefs(other, scope.prefix, scope.names, refs);
    if (std::find(refs.begin(), refs.end(), q) != refs.end()) continue;
    if (side == rel->rhs) ComparisonKind(MirrorComparison(rel->op), cmp);
    name = q;
    return side;
  }
  return nullptr;
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
    return EvalJointTrial(rel, owner, *jr, rc, vals).IsTruthy();
  };
  // 18.5.8: a comparison of one joint variable against an expression over
  // the others derives it from them once they are drawn, as a relation of a
  // single object does (18.3), the solver's repair applying it.
  ConstraintKind cmp = ConstraintKind::kEqual;
  std::string name;
  if (const Expr* derived = DerivedJointSide(rel, scope, cmp, name)) {
    const Expr* other = derived == rel->lhs ? rel->rhs : rel->lhs;
    ce.var_name = name;
    ce.derive_cmp = cmp;
    ce.derive_fn = [other, owner, jr, name,
                    &rc](const std::unordered_map<std::string, int64_t>& vals) {
      Logic4Vec value = EvalJointTrial(other, owner, *jr, rc, vals);
      int64_t v = value.is_signed ? SignExtend(value.ToUint64(), value.width)
                                  : static_cast<int64_t>(value.ToUint64());
      return HeldToVariable(v, name, rc);
    };
  }
  return ce;
}

// A comparison whose other side is a genuine constant (no joint variable) keeps
// the folding/seeding fast path -- qualified to the owner's path and evaluated
// in the owner's scope -- so an equality or bound is still hit reliably; this
// is also how a global constraint against a state variable (rule c) is handled,
// its held value folded in as the constant. False means the relation ties two
// joint variables together, or is not a plain comparison.
bool TryJointComparison(const Expr* rel, const JointVarScope& scope,
                        RandomizeCtx& rc, ConstraintExpr& out, bool fold) {
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
  Logic4Vec cv;
  {
    ConstraintEvalScope eval_scope(scope.owner, rc.ctx);
    cv = EvalExpr(const_side, rc.ctx, rc.arena);
  }
  rc.ctx.PopScope();
  auto c = static_cast<int64_t>(cv.ToUint64());
  out.kind = kind;
  out.var_name = vname;
  out.lo = c;
  out.ref_vars.push_back(vname);
  // 18.4.1: a real variable's bound narrows its real range as a single
  // object's does; 18.9, not one of a block turned off, whose relations are
  // not considered.
  if (fold) FoldComparison(scope.rands, vname, kind, cv, c);
  return true;
}

// 18.5.4: `x inside { ... }` over a joint variable, bare or as handle.field,
// and items free of joint variables, as the set membership the solver draws
// a member of, the items evaluated in the owner's scope; false for any
// other shape.
bool TryJointSetMembership(const Expr* rel, const JointVarScope& scope,
                           RandomizeCtx& rc, ConstraintExpr& out) {
  if (rel == nullptr || rel->kind != ExprKind::kInside || rel->lhs == nullptr)
    return false;
  std::string name = ResolveJointOperand(rel->lhs, scope.prefix, scope.names);
  if (name.empty()) return false;
  for (const Expr* item : rel->elements)
    if (RefsJointVar(item, scope.prefix, scope.names)) return false;
  std::vector<int64_t> values;
  rc.ctx.PushScope();
  bool enumerated =
      EnumerateInsideItems(rel->elements, scope.owner, rc, values);
  rc.ctx.PopScope();
  if (!enumerated) return false;
  out.kind = ConstraintKind::kSetMembership;
  out.var_name = name;
  out.set_values = std::move(values);
  out.ref_vars.push_back(name);
  return true;
}

// 18.5.8: translate one relation of an object's constraint for the joint solve.
// Any relation the comparison fast path above does not take becomes a custom
// joint constraint checked against trial values.
ConstraintExpr BuildJointRelation(const Expr* rel, const JointVarScope& scope,
                                  RandomizeCtx& rc, bool fold) {
  ConstraintExpr out;
  if (TryJointComparison(rel, scope, rc, out, fold)) return out;
  if (TryJointSetMembership(rel, scope, rc, out)) return out;
  // 18.5: `a && b` holds where both do, so each side is built on its own
  // under an antecedent that always holds, a comparison among them folding
  // the domain as it would alone; a real variable's range constraint is
  // written so, and tried against as one relation it could never be met,
  // the trial values carrying no real.
  if (rel != nullptr && rel->kind == ExprKind::kBinary &&
      rel->op == TokenKind::kAmpAmp && rel->lhs != nullptr &&
      rel->rhs != nullptr) {
    out.kind = ConstraintKind::kImplication;
    out.ref_vars.assign(scope.names.begin(), scope.names.end());
    out.cond_fn = [](const std::unordered_map<std::string, int64_t>&) {
      return true;
    };
    out.sub_constraints.push_back(
        BuildJointRelation(rel->lhs, scope, rc, fold));
    out.sub_constraints.push_back(
        BuildJointRelation(rel->rhs, scope, rc, fold));
    return out;
  }
  ConstraintExpr out_custom = MakeJointCustomConstraint(rel, scope, rc);
  // 18.5.12: an implication's antecedent is its constraint guard, resolved
  // before the relation is imposed; a subexpression over a joint variable is
  // RANDOM, any other evaluated over the state in the owner's scope.
  AttachConstraintGuard(
      rel,
      [&scope](const Expr* e) {
        return RefsJointVar(e, scope.prefix, scope.names);
      },
      scope.owner, rc, out_custom);
  return out_custom;
}

// 18.5.8 rule b: select the active constraints of every object in the tree.
// Each object's constraint blocks are collected the same way as for a single
// object (a same-named derived block replaces an inherited one) and translated
// into the shared solver. Only relational constraint expressions are carried
// through the joint path; the tree cases that arise relate simple relational
// and equality constraints, so dist/soft/foreach constraints on a nested object
// are left to the per-object path and not reached here.
// One constraint member of one class level, translated into a solver block.
// 18.5.13.2: each 'disable soft' directive of the block, naming the joint
// variable of the object's member, ahead of the block's own soft
// constraints; 18.5.13: each soft constraint, its inner relation translated
// without folding the draw domain and wrapped in a kSoft the solver honors
// where it can and discards, by its priority (18.5.13.1), where it cannot.
void AddJointSoftConstraints(const ClassMember* m, const JointVarScope& scope,
                             RandomizeCtx& rc, ConstraintBlock& block) {
  for (const auto& ref : m->constraint_disable_soft_refs) {
    ConstraintExpr ce;
    ce.kind = ConstraintKind::kDisableSoft;
    ce.var_name = scope.prefix + std::string(ref.name);
    block.constraints.push_back(std::move(ce));
  }
  for (const Expr* rel : m->constraint_soft_exprs) {
    auto inner = std::make_unique<ConstraintExpr>(
        BuildJointRelation(rel, scope, rc, /*fold=*/false));
    ConstraintExpr sc;
    sc.kind = ConstraintKind::kSoft;
    sc.var_name = inner->var_name;
    sc.ref_vars = inner->ref_vars;
    sc.inner = inner.get();
    rc.soft_inners.push_back(std::move(inner));
    block.constraints.push_back(std::move(sc));
  }
}

void AddJointConstraintBlock(const ClassMember* m, ClassObject* obj,
                             const JointVarScope& scope, RandomizeCtx& rc,
                             ConstraintSolver& solver) {
  ConstraintBlock block;
  block.name = std::string(m->name);
  // 18.9: a block turned off by constraint_mode() is not considered, so its
  // relations fold no bound into the variables' domains.
  block.enabled = IsObjectConstraintActive(obj, m->name);
  for (const Expr* rel : m->constraint_exprs) {
    block.constraints.push_back(
        BuildJointRelation(rel, scope, rc, /*fold=*/block.enabled));
  }
  AddJointSoftConstraints(m, scope, rc, block);
  solver.AddConstraintBlock(block);
}

// Whether a constraint member has a body the joint solve acts on.
bool JointConstraintContributes(const ClassMember* m) {
  return !m->constraint_exprs.empty() || !m->constraint_soft_exprs.empty() ||
         !m->constraint_disable_soft_refs.empty();
}

// 18.5.8 rule b: the active constraints of one object of the tree, its
// class levels added base first (18.5.13.1: a derived class's constraints
// have higher soft priority than its superclasses'), a same-named derived
// block replacing the inherited one (18.5.2).
void CollectJointConstraints(const JointObject& jo,
                             std::vector<RandInfo>& rands,
                             const std::unordered_set<std::string>& names,
                             RandomizeCtx& rc, ConstraintSolver& solver) {
  const JointVarScope kScope{jo.obj, jo.prefix, rands, names};
  for (const ClassMember* m : ConstraintMembersInOrder(jo.obj->type)) {
    if (JointConstraintContributes(m))
      AddJointConstraintBlock(m, jo.obj, kScope, rc, solver);
  }
}

// 18.5.13.1: the objects of the tree in the order their constraints take
// soft priority, lowest first: the constraints in a contained object have
// lower priority than all constraints in its container, and those in
// objects whose handles are declared later in the container have higher
// priority, an object contained more than once taking the priority of the
// handle declared last. So each object follows the subtrees under its
// handles in declaration order, an object reached again moving to its
// later place, and the root comes last.
void SoftPriorityOrder(ClassObject* obj, SimContext& ctx,
                       std::vector<ClassObject*>& out,
                       std::unordered_set<const ClassObject*>& on_path) {
  if (obj == nullptr || obj->type == nullptr || !on_path.insert(obj).second)
    return;
  std::vector<std::string> handles;
  CollectRandObjectMembers(obj->type, ctx, handles);
  for (const auto& name : handles) {
    if (!IsObjectRandActive(obj, name)) continue;
    auto it = obj->properties.find(name);
    if (it == obj->properties.end()) continue;
    SoftPriorityOrder(ctx.GetClassObject(it->second.ToUint64()), ctx, out,
                      on_path);
  }
  on_path.erase(obj);
  auto seen = std::find(out.begin(), out.end(), obj);
  if (seen != out.end()) out.erase(seen);
  out.push_back(obj);
}

// The objects of `objects` in soft-priority order, each with its prefix.
std::vector<const JointObject*> InSoftPriorityOrder(
    const std::vector<JointObject>& objects, SimContext& ctx) {
  std::vector<ClassObject*> ordered;
  std::unordered_set<const ClassObject*> on_path;
  SoftPriorityOrder(objects.front().obj, ctx, ordered, on_path);
  std::vector<const JointObject*> out;
  for (ClassObject* obj : ordered) {
    for (const auto& jo : objects) {
      if (jo.obj == obj) {
        out.push_back(&jo);
        break;
      }
    }
  }
  return out;
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
    Logic4Vec lv = SolvedValue(ri, solver, arena);
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
                         const std::vector<JointObject>& objects,
                         const ClassMember* inline_block) {
  ClassObject* root = objects.front().obj;
  auto seed = static_cast<uint32_t>(ctx.ObjectRng(root)());
  ConstraintSolver solver(seed);
  RandomizeCtx rc{root, ctx, arena};
  rc.solver = &solver;

  std::vector<RandInfo> rands;
  CollectJointRandVariables(objects, ctx, rands);
  std::unordered_set<std::string> names;
  for (const auto& ri : rands) names.insert(ri.name);

  // 18.5.13.1: the solver ranks soft priority by the order the blocks are
  // added, so the objects are added in that order, and the inline block,
  // which outranks every constraint of the class being randomized, last.
  for (const JointObject* jo : InSoftPriorityOrder(objects, ctx))
    CollectJointConstraints(*jo, rands, names, rc, solver);
  if (inline_block != nullptr) {
    const JointVarScope kRootScope{root, objects.front().prefix, rands, names};
    AddJointConstraintBlock(inline_block, root, kRootScope, rc, solver);
  }

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
