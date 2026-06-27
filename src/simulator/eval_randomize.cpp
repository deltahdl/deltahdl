#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
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
  RandVariable var;
};

// State threaded through the randomize() build helpers; bundled to keep helper
// parameter lists small.
struct RandomizeCtx {
  ClassObject* obj;
  SimContext& ctx;
  Arena& arena;
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
  info.var.name = info.name;
  info.var.qualifier =
      m->is_randc ? RandQualifier::kRandc : RandQualifier::kRand;
  uint32_t width = EvalTypeWidth(m->data_type);
  info.var.width = width == 0 ? 32 : width;
  out.push_back(std::move(info));
}

// 18.4: gather every rand/randc data member visible on the object, walking the
// inheritance chain so inherited random variables are included.
void CollectRandVariables(const ClassTypeInfo* type,
                          std::vector<RandInfo>& out) {
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kProperty && (m->is_rand || m->is_randc))
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
                             RandomizeCtx& rc, ConstraintExpr& out) {
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
                                 RandomizeCtx& rc) {
  ConstraintExpr ce;
  if (TryComparisonConstraint(rel, rands, rc, ce)) return ce;
  return MakeCustomConstraint(rel, rands, rc);
}

void AddConstraintMember(const ClassMember* m, std::vector<RandInfo>& rands,
                         RandomizeCtx& rc, ConstraintSolver& solver) {
  ConstraintBlock block;
  block.name = std::string(m->name);
  block.constraints.reserve(m->constraint_exprs.size());
  for (const Expr* rel : m->constraint_exprs) {
    block.constraints.push_back(TranslateRelation(rel, rands, rc));
  }
  solver.AddConstraintBlock(block);
}

// 18.5: build the constraint block(s) from the captured relations of every
// constraint member on the object's class hierarchy.
void CollectConstraintBlocks(const ClassTypeInfo* type,
                             std::vector<RandInfo>& rands, RandomizeCtx& rc,
                             ConstraintSolver& solver) {
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind == ClassMemberKind::kConstraint &&
          !m->constraint_exprs.empty())
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

// 18.6.2: pre_randomize()/post_randomize() are invoked by randomize() before
// and after solving. They are resolved on the object's actual class; the solver
// sequences them and skips post_randomize() on failure (18.6.3).
void RegisterPrePostRandomize(ClassObject* obj, const Expr* expr,
                              SimContext& ctx, Arena& arena,
                              ConstraintSolver& solver) {
  if (ModuleItem* pre = obj->ResolveMethod("pre_randomize")) {
    solver.SetPreRandomize([pre, obj, expr, &ctx, &arena] {
      ExecInstanceMethodCall(pre, obj, expr, ctx, arena);
    });
  }
  if (ModuleItem* post = obj->ResolveMethod("post_randomize")) {
    solver.SetPostRandomize([post, obj, expr, &ctx, &arena] {
      ExecInstanceMethodCall(post, obj, expr, ctx, arena);
    });
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

}  // namespace

bool TryEvalRandomizeMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (parts.method_name != "randomize") return false;
  ClassObject* obj = ResolveRandomizeTarget(ctx, parts);
  if (!obj) return false;

  // 18.6.3: seed from the object's own RNG so randomize() draws a fresh result
  // each call while staying reproducible from the object's starting state.
  auto seed = static_cast<uint32_t>(ctx.ObjectRng(obj)());
  ConstraintSolver solver(seed);
  RandomizeCtx rc{obj, ctx, arena};

  std::vector<RandInfo> rands;
  CollectRandVariables(obj->type, rands);
  CollectConstraintBlocks(obj->type, rands, rc, solver);
  for (auto& ri : rands) {
    if (ri.var.min_val > ri.var.max_val) ri.var.max_val = ri.var.min_val;
    solver.AddVariable(ri.var);
  }
  RegisterPrePostRandomize(obj, expr, ctx, arena, solver);

  bool solved = solver.SolveWith({});
  if (solved) WriteBackSolved(obj, rands, solver, arena);
  out = MakeLogic4VecVal(arena, 32, solved ? 1 : 0);
  return true;
}

}  // namespace delta
