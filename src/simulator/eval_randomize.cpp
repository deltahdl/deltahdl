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
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {
namespace {

// A rand/randc variable discovered on the randomized object, paired with the
// class level that declares it (for the scoped "Class::name" property alias)
// and the solver variable being built for it.
struct RandInfo {
  std::string name;
  const ClassTypeInfo* level = nullptr;
  // 18.4.2: a static randc shares its cyclic permutation across every instance
  // of the declaring class, so its history is stored on the (shared) class type
  // rather than on the object. Track the static-ness of the source member here.
  bool is_static = false;
  RandVariable var;
};

// State threaded through the randomize() build helpers; bundled to keep helper
// parameter lists small.
struct RandomizeCtx {
  ClassObject* obj;
  SimContext& ctx;
  Arena& arena;
  // 18.5.13: stable storage for the inner relation of each soft constraint. A
  // kSoft ConstraintExpr points to its inner relation through a raw pointer, so
  // the inner must outlive the solve; owning it on the heap here keeps that
  // address stable even as the solver copies the block holding the kSoft.
  std::vector<std::unique_ptr<ConstraintExpr>> soft_inners;
};

RandInfo* FindRand(std::vector<RandInfo>& rands, std::string_view name) {
  for (auto& ri : rands) {
    if (std::string_view(ri.name) == name) return &ri;
  }
  return nullptr;
}

// 18.4: build a solver variable for one rand/randc data member. The default
// integral domain is later tightened by the relational constraints.
void AddRandMember(const ClassMember* m, const ClassTypeInfo* level,
                   std::vector<RandInfo>& out) {
  RandInfo info;
  info.name = std::string(m->name);
  info.level = level;
  info.is_static = m->is_static;
  info.var.name = info.name;
  info.var.qualifier =
      m->is_randc ? RandQualifier::kRandc : RandQualifier::kRand;
  uint32_t width = EvalTypeWidth(m->data_type);
  info.var.width = width == 0 ? 32 : width;
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
        AddRandMember(m, lvl, out);
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

// 18.5: translate one captured constraint relation into a solver
// ConstraintExpr.
ConstraintExpr TranslateRelation(const Expr* rel, std::vector<RandInfo>& rands,
                                 RandomizeCtx& rc, bool fold = true) {
  ConstraintExpr ce;
  if (TryComparisonConstraint(rel, rands, rc, ce, fold)) return ce;
  return MakeCustomConstraint(rel, rands, rc);
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

// 18.8: report whether a random variable is active on this object. Every
// rand/randc variable is active when the object is created, so an absent entry
// means active; an explicit entry records the last rand_mode() setting.
bool IsObjectRandActive(const ClassObject* obj, std::string_view name) {
  auto it = obj->rand_active.find(std::string(name));
  return it == obj->rand_active.end() ? true : it->second;
}

// 18.8 / Table 18-3: record a random variable's active (ON) or inactive (OFF)
// state for this object, as set by a rand_mode() call.
void SetObjectRandActive(ClassObject* obj, std::string_view name, bool active) {
  obj->rand_active[std::string(name)] = active;
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

void AddConstraintMember(const ClassMember* m, std::vector<RandInfo>& rands,
                         RandomizeCtx& rc, ConstraintSolver& solver) {
  ConstraintBlock block;
  block.name = std::string(m->name);
  block.constraints.reserve(
      m->constraint_exprs.size() + m->constraint_dist_refs.size() +
      m->constraint_soft_exprs.size() + m->constraint_soft_dist_refs.size());
  for (const Expr* rel : m->constraint_exprs) {
    block.constraints.push_back(TranslateRelation(rel, rands, rc));
  }
  // 18.5.3: build each captured distribution as a weighted-value constraint.
  for (const auto& ref : m->constraint_dist_refs) {
    ConstraintExpr ce;
    if (BuildDistConstraint(ref, rc, ce)) block.constraints.push_back(ce);
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
  std::unordered_set<std::string_view> replaced;
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind != ClassMemberKind::kConstraint) continue;
      if (!replaced.insert(m->name).second) continue;
      if (!m->constraint_exprs.empty() || !m->constraint_dist_refs.empty() ||
          !m->constraint_soft_exprs.empty() ||
          !m->constraint_soft_dist_refs.empty())
        AddConstraintMember(m, rands, rc, solver);
    }
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

// 18.6.1: write each solved value back to the object, keeping the bare and
// scoped ("Class::name") property aliases in sync so member reads see it.
void WriteBackSolved(ClassObject* obj, std::vector<RandInfo>& rands,
                     ConstraintSolver& solver, Arena& arena) {
  for (auto& ri : rands) {
    if (ri.var.is_real) continue;
    int64_t v = solver.GetValue(ri.name);
    Logic4Vec lv =
        MakeLogic4VecVal(arena, ri.var.width, static_cast<uint64_t>(v));
    obj->properties[ri.name] = lv;
    obj->properties[std::string(ri.level->name) + "::" + ri.name] = lv;
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

// 18.6.1: randomize() sets all of an object's active random variables AND the
// random objects it references to valid values, succeeding only when every one
// is solved. Solve this object's own random variables subject to its active
// constraints and write the results back, then recurse into each non-null rand
// object-handle member so its own random members are randomized as well; the
// overall result fails if any sub-object solve fails. The visited set breaks
// handle cycles so a self- or mutually-referential object graph terminates. A
// null random object handle references nothing to randomize and is skipped.
bool RandomizeObject(ClassObject* obj, SimContext& ctx, Arena& arena,
                     const Expr* expr, const ClassMember* inline_block,
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
    // 18.8: a variable turned inactive by rand_mode() is not randomized; the
    // solver treats it as a state variable, holding its current value constant.
    // Seed that value and disable the variable so the solve leaves it untouched
    // while still evaluating any constraint that relates to it. This is a
    // per-object flag set from real rand_mode() calls, so it persists across
    // successive randomize() calls until rand_mode() re-enables the variable.
    if (!IsObjectRandActive(obj, ri.name)) {
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

  std::vector<std::string> object_members;
  CollectRandObjectMembers(obj->type, ctx, object_members);
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
                         visited))
      solved = false;
  }
  return solved;
}

}  // namespace

bool TryEvalRandomizeMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (parts.method_name != "randomize") return false;
  ClassObject* obj = ResolveRandomizeTarget(ctx, parts);
  if (!obj) return false;

  std::unordered_set<const ClassObject*> visited;
  bool solved =
      RandomizeObject(obj, ctx, arena, expr, expr->inline_constraint, visited);
  out = MakeLogic4VecVal(arena, 32, solved ? 1 : 0);
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
    for (const auto* lvl = obj->type; lvl != nullptr; lvl = lvl->parent) {
      if (!lvl->decl) continue;
      for (const ClassMember* m : lvl->decl->members) {
        if (m->kind == ClassMemberKind::kConstraint)
          SetObjectConstraintActive(obj, m->name, on);
      }
    }
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
    for (const auto* lvl = obj->type; lvl != nullptr; lvl = lvl->parent) {
      if (!lvl->decl) continue;
      for (const ClassMember* m : lvl->decl->members) {
        if (m->kind == ClassMemberKind::kProperty &&
            (m->is_rand || m->is_randc))
          SetObjectRandActive(obj, m->name, on);
      }
    }
  } else {
    SetObjectRandActive(obj, var_name, on);
  }
  out = MakeLogic4VecVal(arena, 1, 0);
  return true;
}

}  // namespace delta
