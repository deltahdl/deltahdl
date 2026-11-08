#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/types.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"

namespace delta {

static void AddDisableSoftDirectives(const ClassMember* m,
                                     ConstraintBlock& block) {
  for (const auto& ref : m->constraint_disable_soft_refs) {
    ConstraintExpr ce;
    ce.kind = ConstraintKind::kDisableSoft;
    ce.var_name = std::string(ref.name);
    block.constraints.push_back(std::move(ce));
  }
}

static void AddSoftConstraints(const ClassMember* m,
                               std::vector<RandInfo>& rands, RandomizeCtx& rc,
                               ConstraintBlock& block) {
  for (const Expr* rel : m->constraint_soft_exprs) {
    bool gated = rel->kind == ExprKind::kBinary &&
                 rel->op == TokenKind::kArrow && rel->lhs != nullptr &&
                 rel->rhs != nullptr;
    auto inner = std::make_unique<ConstraintExpr>();
    if (!gated) {
      *inner = TranslateRelation(rel, rands, rc, false);
    } else if (!TryJointRelation(rel, rands, rc, false, *inner)) {
      *inner = SoftImplication(rel, rands, rc);
    }
    ConstraintExpr sc;
    sc.kind = ConstraintKind::kSoft;
    sc.var_name = inner->var_name;
    sc.ref_vars = inner->ref_vars;
    sc.inner = inner.get();
    rc.soft_inners.push_back(std::move(inner));
    block.constraints.push_back(std::move(sc));
  }
}

static void AddSoftDistConstraints(const ClassMember* m, RandomizeCtx& rc,
                                   ConstraintBlock& block) {
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
}

static void AddUniqueName(std::string_view name, std::vector<RandInfo>& rands,
                          std::vector<std::string>& out) {
  if (FindRand(rands, name)) {
    out.push_back(std::string(name));
    return;
  }
  for (const auto& ri : rands) {
    if (ri.array_base == name && !ri.var.is_array_size) out.push_back(ri.name);
  }
}

static void AddUniqueSelect(const Expr* item, std::vector<RandInfo>& rands,
                            RandomizeCtx& rc, std::vector<std::string>& out) {
  auto bound = [&rc](const Expr* e) {
    ConstraintEvalScope scope(rc.obj, rc.ctx);
    Logic4Vec v = EvalExpr(e, rc.ctx, rc.arena);
    return v.is_signed ? SignExtend(v.ToUint64(), v.width)
                       : static_cast<int64_t>(v.ToUint64());
  };
  int64_t lo = bound(item->index);
  int64_t hi = item->index_end != nullptr ? bound(item->index_end) : lo;
  if (lo > hi) std::swap(lo, hi);
  for (int64_t i = lo; i <= hi; ++i) {
    std::string name = ClassArrayElementKey(item->base->text, i);
    if (FindRand(rands, name)) out.push_back(name);
  }
}

static void AddUniqueMember(const Expr* item, std::vector<RandInfo>& rands,
                            RandomizeCtx& rc, std::vector<std::string>& out) {
  if (item == nullptr) return;
  if (item->kind == ExprKind::kIdentifier) {
    AddUniqueName(item->text, rands, out);
  } else if (item->kind == ExprKind::kSelect && item->base != nullptr &&
             item->base->kind == ExprKind::kIdentifier &&
             item->index != nullptr) {
    AddUniqueSelect(item, rands, rc, out);
  } else if (item->kind == ExprKind::kMemberAccess) {
    std::string name = JointVariableName(item, rc);
    if (!name.empty()) out.push_back(std::move(name));
  }
}

static void AddUniqueConstraints(const ClassMember* m,
                                 std::vector<RandInfo>& rands, RandomizeCtx& rc,
                                 ConstraintBlock& block) {
  for (const auto& group : m->constraint_unique_refs) {
    ConstraintExpr ce;
    ce.kind = ConstraintKind::kUnique;
    for (const Expr* item : group)
      AddUniqueMember(item, rands, rc, ce.unique_vars);
    ce.ref_vars = ce.unique_vars;
    block.constraints.push_back(std::move(ce));
  }
}

static std::vector<std::string> ResolveOrderedNames(
    const std::vector<ConstraintSolveBeforeEntry>& entries,
    std::vector<RandInfo>& rands, const RandomizeCtx& rc) {
  std::vector<std::string> names;
  for (const auto& e : entries) {
    if (e.is_simple && FindRand(rands, e.name)) {
      names.push_back(std::string(e.name));
      continue;
    }
    if (e.handles.empty()) continue;
    std::string path;
    for (std::string_view handle : e.handles) path += std::string(handle) + ".";
    path += e.name;
    if (IsJointVariable(path, rc)) names.push_back(std::move(path));
  }
  return names;
}

static void AddSolveBeforeOrderings(const ClassMember* m,
                                    std::vector<RandInfo>& rands,
                                    const RandomizeCtx& rc,
                                    ConstraintSolver& solver) {
  for (const auto& ref : m->constraint_solve_before_refs) {
    std::vector<std::string> before =
        ResolveOrderedNames(ref.before, rands, rc);
    std::vector<std::string> after = ResolveOrderedNames(ref.after, rands, rc);
    if (!before.empty() && !after.empty()) solver.AddSolveBefore(before, after);
  }
}

static std::vector<std::string> FilterRandNames(
    const std::unordered_set<std::string>& names,
    const std::unordered_set<std::string>* excluded,
    std::vector<RandInfo>& rands) {
  std::vector<std::string> out;
  for (const auto& n : names) {
    if (excluded != nullptr && excluded->find(n) != excluded->end()) continue;
    if (FindRand(rands, n)) out.push_back(n);
  }
  return out;
}

static void AddFunctionArgPriorities(const ClassMember* m,
                                     std::vector<RandInfo>& rands,
                                     ConstraintSolver& solver) {
  for (const Expr* rel : m->constraint_exprs) {
    std::unordered_set<std::string> all_names;
    std::unordered_set<std::string> arg_names;
    CollectConstraintArgRefs(rel, false, all_names, arg_names);
    std::vector<std::string> higher =
        FilterRandNames(arg_names, nullptr, rands);
    if (higher.empty()) continue;
    std::vector<std::string> lower =
        FilterRandNames(all_names, &arg_names, rands);
    if (!lower.empty()) solver.AddFunctionArgPriority(higher, lower);
  }
}

void AddConstraintMember(const ClassMember* m, std::vector<RandInfo>& rands,
                         RandomizeCtx& rc, ConstraintSolver& solver) {
  ConstraintBlock block;
  block.name = std::string(m->name);
  block.enabled = IsObjectConstraintActive(rc.obj, m->name);
  block.constraints.reserve(
      m->constraint_exprs.size() + m->constraint_dist_refs.size() +
      m->constraint_soft_exprs.size() + m->constraint_soft_dist_refs.size() +
      m->constraint_disable_soft_refs.size());
  for (const Expr* rel : m->constraint_exprs) {
    block.constraints.push_back(
        TranslateRelation(rel, rands, rc, block.enabled));
  }
  AddForeachConstraints(m, rands, rc, block);
  for (const auto& ref : m->constraint_dist_refs) {
    ConstraintExpr ce;
    if (BuildDistConstraint(ref, rc, ce)) block.constraints.push_back(ce);
  }
  AddDisableSoftDirectives(m, block);
  AddSoftConstraints(m, rands, rc, block);
  AddSoftDistConstraints(m, rc, block);
  AddUniqueConstraints(m, rands, rc, block);
  AddSolveBeforeOrderings(m, rands, rc, solver);
  AddFunctionArgPriorities(m, rands, solver);

  solver.AddConstraintBlock(block);
}

static bool ConstraintMemberContributes(const ClassMember* m) {
  return !m->constraint_exprs.empty() || !m->constraint_dist_refs.empty() ||
         !m->constraint_foreach_refs.empty() ||
         !m->constraint_soft_exprs.empty() ||
         !m->constraint_soft_dist_refs.empty() ||
         !m->constraint_unique_refs.empty() ||
         !m->constraint_solve_before_refs.empty() ||
         !m->constraint_disable_soft_refs.empty();
}

static std::vector<const ClassMember*> CollectLevelConstraints(
    const ClassTypeInfo* lvl, std::unordered_set<std::string_view>& replaced) {
  std::vector<const ClassMember*> level_members;
  for (const ClassMember* m : lvl->decl->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    if (!replaced.insert(m->name).second) continue;
    if (ConstraintMemberContributes(m)) level_members.push_back(m);
  }
  return level_members;
}

std::vector<const ClassMember*> ConstraintMembersInOrder(
    const ClassTypeInfo* type) {
  std::unordered_set<std::string_view> replaced;
  std::vector<std::vector<const ClassMember*>> per_level;
  for (const auto* lvl = type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    per_level.push_back(CollectLevelConstraints(lvl, replaced));
  }
  std::vector<const ClassMember*> members;
  for (auto it = per_level.rbegin(); it != per_level.rend(); ++it)
    members.insert(members.end(), it->begin(), it->end());
  return members;
}

void CollectConstraintBlocks(const ClassTypeInfo* type,
                             std::vector<RandInfo>& rands, RandomizeCtx& rc,
                             ConstraintSolver& solver) {
  for (const ClassMember* m : ConstraintMembersInOrder(type))
    AddConstraintMember(m, rands, rc, solver);
}

}  // namespace delta
