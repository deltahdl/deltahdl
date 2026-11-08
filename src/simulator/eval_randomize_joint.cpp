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

std::string ResolveJointOperand(const Expr* e,
                                const std::unordered_set<std::string>& names) {
  std::string q = OperandPath(e);
  return names.count(q) != 0 ? q : std::string{};
}

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

struct SavedJointProperty {
  ClassObject* obj;
  std::string key;
  bool had;
  Logic4Vec old;
};

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

void RestoreJointProperties(const std::vector<SavedJointProperty>& saved) {
  for (auto it = saved.rbegin(); it != saved.rend(); ++it) {
    if (it->had)
      it->obj->properties[it->key] = it->old;
    else
      it->obj->properties.erase(it->key);
  }
}

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
  if (fold) FoldComparison(scope.rands, vname, kind, cv, c);
  return true;
}

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

bool TryJointImplication(const Expr* rel, JointVarScope& scope,
                         RandomizeCtx& rc, ConstraintExpr& out) {
  if (rel->kind != ExprKind::kBinary || rel->op != TokenKind::kArrow)
    return false;
  ConstraintExpr consequent = BuildJointRelation(rel->rhs, scope, rc, false);
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

ConstraintExpr BuildJointRelation(const Expr* rel, JointVarScope& scope,
                                  RandomizeCtx& rc, bool fold) {
  ConstraintExpr out;
  if (TryJointComparison(rel, scope, rc, out, fold)) return out;
  if (TryJointSetMembership(rel, scope, rc, out)) return out;
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

std::vector<ObjectSolve> TreeParts(const std::vector<JointObject>& objects,
                                   const ClassMember* inline_block,
                                   ConstraintSolver& solver, SimContext& ctx,
                                   Arena& arena) {
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
