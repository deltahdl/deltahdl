#include <algorithm>
#include <cstdint>
#include <memory>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/eval_class_array.h"
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
// referential graph terminates. 18.6.2: each object's pre_randomize() runs
// before its handles are read, so an object it allocates or replaces is the
// one the tree takes.
//
// The randomize() call the tree is gathered for, and the tree so far.
struct TreeWalk {
  const Expr* expr;
  SimContext& ctx;
  Arena& arena;
  std::vector<JointObject> out = {};
  std::unordered_set<const ClassObject*> visited = {};
};

void GatherTree(ClassObject* obj, const std::string& prefix, TreeWalk& walk) {
  if (!obj || !obj->type) return;
  if (!walk.visited.insert(obj).second) return;
  InvokePreRandomize(obj, walk.expr, walk.ctx, walk.arena);
  walk.out.push_back({obj, prefix});
  for (const auto& [key, sub] : ActiveRandObjectMembers(obj, walk.ctx))
    GatherTree(sub, prefix + key + ".", walk);
}

std::vector<JointObject> CollectActiveRandomObjects(ClassObject* obj,
                                                    const Expr* expr,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  TreeWalk walk{expr, ctx, arena};
  GatherTree(obj, "", walk);
  return std::move(walk.out);
}

// 18.5.8: the path an operand names from the object whose relation it is
// in: a bare identifier as written, a select of an array at a literal index,
// `arr[1]`, by the key its element is held under, and a member of either
// through a handle, `left.v` or `arr[1].y`, as the path to the handle, a dot
// and the member; empty for any other form.
std::string OperandPath(const Expr* e) {
  if (e == nullptr) return {};
  if (e->kind == ExprKind::kIdentifier) return std::string(e->text);
  if (e->kind == ExprKind::kSelect && e->index_end == nullptr &&
      e->base != nullptr && e->base->kind == ExprKind::kIdentifier &&
      e->index != nullptr && e->index->kind == ExprKind::kIntegerLiteral) {
    return ClassArrayElementKey(e->base->text,
                                static_cast<int64_t>(e->index->int_val));
  }
  if (e->kind != ExprKind::kMemberAccess || e->is_scope_resolution ||
      e->rhs == nullptr || e->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  std::string handle = OperandPath(e->lhs);
  if (handle.empty()) return {};
  return handle + "." + std::string(e->rhs->text);
}

// 18.5.8: resolve a constraint operand to the name of a joint rand variable
// within the constraint's object, or an empty string when the operand is not
// one (a state variable, whose present value the solver reads as fixed).
std::string ResolveJointOperand(const Expr* e,
                                const std::unordered_set<std::string>& names) {
  std::string q = OperandPath(e);
  return names.count(q) != 0 ? q : std::string{};
}

// 18.5.8: true when an expression references any joint rand variable, so it is
// not a solve-time constant. An operand naming one is resolved as a whole --
// the field of a member access is never treated as a bare-identifier operand,
// so a nested `.v` is not confused with a same-named variable of the
// constraint's own object.
bool RefsJointVar(const Expr* e, const std::unordered_set<std::string>& names) {
  if (e == nullptr) return false;
  if (!ResolveJointOperand(e, names).empty()) return true;
  if (e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kMemberAccess)
    return false;
  if (RefsJointVar(e->lhs, names)) return true;
  if (RefsJointVar(e->rhs, names)) return true;
  if (RefsJointVar(e->base, names)) return true;
  for (const Expr* a : e->args)
    if (RefsJointVar(a, names)) return true;
  return false;
}

// 18.5.8: collect the names of the joint variables an expression references
// (for the priority/ordered passes; the flat pass checks every constraint
// regardless). An operand naming one is taken whole so a member access's
// field is not walked as a separate identifier.
void CollectJointRefs(const Expr* e,
                      const std::unordered_set<std::string>& names,
                      std::vector<std::string>& out) {
  if (e == nullptr) return;
  std::string q = ResolveJointOperand(e, names);
  if (!q.empty()) {
    out.push_back(q);
    return;
  }
  if (e->kind == ExprKind::kIdentifier || e->kind == ExprKind::kMemberAccess)
    return;
  CollectJointRefs(e->lhs, names, out);
  CollectJointRefs(e->rhs, names, out);
  CollectJointRefs(e->base, names, out);
  for (const Expr* a : e->args) CollectJointRefs(a, names, out);
}

// 18.5.8: build a custom joint constraint. A global constraint relates random
// variables from different objects, so it cannot fold one side into a domain
// bound; instead it is checked against trial values. On each evaluation the
// trial value of every joint variable is written into its owning object's
// property, the relation is evaluated in the owner's scope so a member access
// like left.v reads the trial value from the referenced object, and the
// original property values are restored. This lets the solver see every
// referenced variable at its trial value simultaneously, which is what solving
// the variables together requires.
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
const Expr* DerivedJointSide(const Expr* rel, JointVarScope& scope,
                             ConstraintKind& cmp, std::string& name) {
  if (rel->kind != ExprKind::kBinary || rel->lhs == nullptr ||
      rel->rhs == nullptr || rel->op == TokenKind::kBangEq ||
      !ComparisonKind(rel->op, cmp)) {
    return nullptr;
  }
  for (const Expr* side : {rel->lhs, rel->rhs}) {
    const Expr* other = side == rel->lhs ? rel->rhs : rel->lhs;
    std::string q = ResolveJointOperand(side, scope.names);
    if (q.empty()) continue;
    std::vector<std::string> refs;
    CollectJointRefs(other, scope.names, refs);
    if (std::find(refs.begin(), refs.end(), q) != refs.end()) continue;
    if (side == rel->rhs) ComparisonKind(MirrorComparison(rel->op), cmp);
    name = q;
    return side;
  }
  return nullptr;
}

ConstraintExpr MakeJointCustomConstraint(const Expr* rel, JointVarScope& scope,
                                         RandomizeCtx& rc) {
  ConstraintExpr ce;
  ce.kind = ConstraintKind::kCustom;
  CollectJointRefs(rel, scope.names, ce.ref_vars);
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
    ce.co_var_name = ResolveJointOperand(other, scope.names);
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
bool TryJointComparison(const Expr* rel, JointVarScope& scope, RandomizeCtx& rc,
                        ConstraintExpr& out, bool fold) {
  if (rel == nullptr || rel->kind != ExprKind::kBinary || rel->lhs == nullptr ||
      rel->rhs == nullptr)
    return false;
  ConstraintKind kind = ConstraintKind::kEqual;
  if (!ComparisonKind(rel->op, kind)) return false;
  std::string lname = ResolveJointOperand(rel->lhs, scope.names);
  std::string rname = ResolveJointOperand(rel->rhs, scope.names);
  std::string vname;
  const Expr* const_side = nullptr;
  bool mirror = false;
  if (!lname.empty() && !RefsJointVar(rel->rhs, scope.names)) {
    vname = lname;
    const_side = rel->rhs;
  } else if (!rname.empty() && !RefsJointVar(rel->lhs, scope.names)) {
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
bool TryJointSetMembership(const Expr* rel, JointVarScope& scope,
                           RandomizeCtx& rc, ConstraintExpr& out) {
  if (rel == nullptr || rel->kind != ExprKind::kInside || rel->lhs == nullptr)
    return false;
  std::string name = ResolveJointOperand(rel->lhs, scope.names);
  if (name.empty()) return false;
  for (const Expr* item : rel->elements)
    if (RefsJointVar(item, scope.names)) return false;
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

ConstraintExpr BuildJointRelation(const Expr* rel, JointVarScope& scope,
                                  RandomizeCtx& rc, bool fold);

// 18.5.6: `a -> b` as the solver's implication, its consequent built over
// the joint variables as a relation of its own and imposed where the
// antecedent, evaluated over the trial values, holds. The consequent's
// bounds hold only where the antecedent does, so none of them folds the
// variable's domain. A consequent the solver would try as a whole is left
// to be tried with its antecedent, unless it derives one variable from the
// others; false then, and for any other shape.
bool TryJointImplication(const Expr* rel, JointVarScope& scope,
                         RandomizeCtx& rc, ConstraintExpr& out) {
  if (rel->kind != ExprKind::kBinary || rel->op != TokenKind::kArrow)
    return false;
  ConstraintExpr consequent =
      BuildJointRelation(rel->rhs, scope, rc, /*fold=*/false);
  if (consequent.kind == ConstraintKind::kCustom && !consequent.derive_fn)
    return false;
  out.kind = ConstraintKind::kImplication;
  out.ref_vars.assign(scope.names.begin(), scope.names.end());
  out.cond_fn = [antecedent = rel->lhs, &scope,
                 &rc](const std::unordered_map<std::string, int64_t>& vals) {
    return EvalJointTrial(antecedent, scope.owner, scope.rands, rc, vals)
        .IsTruthy();
  };
  out.sub_constraints.push_back(std::move(consequent));
  return true;
}

// 18.5.8: translate one relation of an object's constraint for the joint solve.
// Any relation the shapes above do not take becomes a custom joint constraint
// checked against trial values.
ConstraintExpr BuildJointRelation(const Expr* rel, JointVarScope& scope,
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
  if (!TryJointImplication(rel, scope, rc, out))
    out = MakeJointCustomConstraint(rel, scope, rc);
  // 18.5.12: an implication's antecedent is its constraint guard, resolved
  // before the relation is imposed; a subexpression over a joint variable is
  // RANDOM, any other evaluated over the state in the owner's scope.
  AttachConstraintGuard(
      rel, [&scope](const Expr* e) { return RefsJointVar(e, scope.names); },
      scope.owner, rc, out);
  return out;
}

bool IsJointVariable(const std::string& name, const RandomizeCtx& rc) {
  return rc.joint != nullptr && rc.joint->names.count(name) != 0;
}

std::string JointVariableName(const Expr* e, const RandomizeCtx& rc) {
  std::string name = OperandPath(e);
  return IsJointVariable(name, rc) ? name : std::string{};
}

// 18.5.8: whether `e` reaches a random variable of another object of the
// tree through a handle, `left.v`, which the per-object machinery would read
// as a state variable; a member access naming one of the object's own
// variables, a member of its rand structure, does not.
bool ReachesAnotherObject(const Expr* e, std::vector<RandInfo>& own,
                          const RandomizeCtx& rc) {
  if (e == nullptr || e->kind == ExprKind::kIdentifier) return false;
  if (e->kind == ExprKind::kMemberAccess) {
    std::string name = JointVariableName(e, rc);
    return !name.empty() && FindRand(own, name) == nullptr;
  }
  for (const Expr* sub :
       {e->lhs, e->rhs, e->base, e->condition, e->true_expr, e->false_expr}) {
    if (ReachesAnotherObject(sub, own, rc)) return true;
  }
  for (const auto* list : {&e->args, &e->elements}) {
    for (const Expr* sub : *list)
      if (ReachesAnotherObject(sub, own, rc)) return true;
  }
  return false;
}

bool TryJointRelation(const Expr* rel, std::vector<RandInfo>& rands,
                      RandomizeCtx& rc, bool fold, ConstraintExpr& out) {
  if (rc.joint == nullptr || !ReachesAnotherObject(rel, rands, rc))
    return false;
  out = BuildJointRelation(rel, *rc.joint, rc, fold);
  return true;
}

// 18.5.13.1: the objects of the tree in the order their constraints take soft
// priority, lowest first: every constraint of a container outranks those of the
// objects it contains, a later-declared handle's object outranks an earlier
// one's, and an object held by several handles ranks with the last of them. So
// each object follows the subtrees under its handles in declaration order, an
// object reached again moving to its later place, and the root comes last.
void SoftPriorityOrder(ClassObject* obj, SimContext& ctx,
                       std::vector<ClassObject*>& out,
                       std::unordered_set<const ClassObject*>& on_path) {
  if (!on_path.insert(obj).second) return;
  for (const auto& [key, sub] : ActiveRandObjectMembers(obj, ctx))
    SoftPriorityOrder(sub, ctx, out, on_path);
  on_path.erase(obj);
  auto seen = std::find(out.begin(), out.end(), obj);
  if (seen != out.end()) out.erase(seen);
  out.push_back(obj);
}

// The parts of the tree in soft-priority order.
std::vector<ObjectSolve*> InSoftPriorityOrder(std::vector<ObjectSolve>& parts,
                                              SimContext& ctx) {
  std::vector<ClassObject*> ordered;
  std::unordered_set<const ClassObject*> on_path;
  SoftPriorityOrder(parts.front().obj, ctx, ordered, on_path);
  std::vector<ObjectSolve*> out;
  for (ClassObject* obj : ordered) {
    auto part =
        std::find_if(parts.begin(), parts.end(),
                     [obj](const ObjectSolve& p) { return p.obj == obj; });
    if (part != parts.end()) out.push_back(&*part);
  }
  return out;
}

// 18.5.8 rule c: each object of the tree with its random variables, gathered
// as for the object alone in a context reading the shared solver under the
// object's prefix; the root's with the call's inline block, which can size
// its arrays (18.4).
std::vector<ObjectSolve> TreeParts(const std::vector<JointObject>& objects,
                                   const ClassMember* inline_block,
                                   ConstraintSolver& solver, SimContext& ctx,
                                   Arena& arena) {
  // The relations built over an object's variables may hold on to its
  // list, so the parts are never moved once built.
  std::vector<ObjectSolve> parts;
  parts.reserve(objects.size());
  for (const auto& jo : objects) {
    ObjectSolve& part = parts.emplace_back();
    part.obj = jo.obj;
    part.prefix = jo.prefix;
    part.rc = std::make_unique<RandomizeCtx>(RandomizeCtx{jo.obj, ctx, arena});
    part.rc->solver = &solver;
    part.rc->solver_prefix = jo.prefix;
    if (parts.size() == 1) part.rc->inline_block = inline_block;
    CollectRandVariables(jo.obj->type, ctx, part.rands);
    AddDynamicArrayVariables(part.rands, *part.rc);
  }
  return parts;
}

// 18.5.8: for each object of the tree, every random variable of the tree
// under its prefix, named within the prefix, with the object holding it, as
// the object's relations reaching across objects read and write them.
void BindJointScopes(std::vector<ObjectSolve>& parts) {
  for (auto& part : parts) {
    part.joint.owner = part.obj;
    for (const auto& held : parts) {
      if (!held.prefix.starts_with(part.prefix)) continue;
      const std::string kPath = held.prefix.substr(part.prefix.size());
      for (RandInfo ri : held.rands) {
        ri.member = ri.name;
        ri.owner = held.obj;
        ri.name = kPath + ri.name;
        ri.var.name = ri.name;
        part.joint.names.insert(ri.name);
        part.joint.rands.push_back(std::move(ri));
      }
    }
    part.rc->joint = &part.joint;
  }
}

// 18.6.2: each object's solved values written back, and only then each
// one's post_randomize(), so each reads every object at its new values.
void CommitParts(std::vector<ObjectSolve>& parts,
                 const ConstraintSolver* shared, const Expr* expr,
                 SimContext& ctx, Arena& arena) {
  for (auto& part : parts) {
    const ConstraintSolver& solver = shared != nullptr ? *shared : *part.solver;
    WriteBackSolved(part.obj, part.rands, solver, part.prefix, arena);
  }
  for (auto& part : parts) InvokePostRandomize(part.obj, expr, ctx, arena);
}

bool RandomizeObjectTree(SimContext& ctx, Arena& arena, const Expr* expr,
                         const std::vector<JointObject>& objects,
                         const ClassMember* inline_block) {
  ClassObject* root = objects.front().obj;
  auto seed = static_cast<uint32_t>(ctx.ObjectRng(root)());
  ConstraintSolver solver(seed);
  std::vector<ObjectSolve> parts =
      TreeParts(objects, inline_block, solver, ctx, arena);
  parts.front().rc->inline_receiver = InlineReceiverName(expr);
  BindJointScopes(parts);

  // 18.5.13.1: the solver ranks soft priority by the order the blocks are
  // added, so the objects are added in that order, and the inline block,
  // which outranks every constraint of the class being randomized, last.
  // 18.5.8: each object's constraints are built as for the object alone
  // under its prefix, a relation reaching another object of the tree over
  // the variables the object reaches.
  for (ObjectSolve* part : InSoftPriorityOrder(parts, ctx)) {
    solver.SetNameScope(part->prefix);
    for (const ClassMember* m : ConstraintMembersInOrder(part->obj->type))
      AddConstraintMember(m, part->rands, *part->rc, solver);
    if (part == &parts.front() && inline_block != nullptr)
      AddConstraintMember(inline_block, part->rands, *part->rc, solver);
  }
  for (auto& part : parts) {
    solver.SetNameScope(part.prefix);
    PrepareRandVariables(part.obj, part.rands, nullptr, solver);
  }
  solver.SetNameScope("");
  if (!solver.SolveWith({})) return false;
  CommitParts(parts, &solver, expr, ctx, arena);
  return true;
}

bool RandomizeEachObject(const std::vector<JointObject>& objects,
                         const InlineRandomizeCall& call, SimContext& ctx,
                         Arena& arena) {
  std::vector<ObjectSolve> parts;
  parts.reserve(objects.size());
  for (const auto& jo : objects) {
    ObjectSolve& part = parts.emplace_back();
    part.obj = jo.obj;
    // The inline block and the argument list are the root's alone.
    InlineRandomizeCall own =
        parts.size() == 1
            ? call
            : InlineRandomizeCall{call.expr, nullptr, nullptr, false};
    if (!SolveObject(part, own, ctx, arena)) return false;
  }
  CommitParts(parts, nullptr, call.expr, ctx, arena);
  return true;
}

}  // namespace delta
