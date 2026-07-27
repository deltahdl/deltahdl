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

// 18.5.13.2: build each 'disable soft var' directive as a kDisableSoft solver
// constraint naming the variable. Emitted before the block's own soft
// constraints so that, in declaration order, the directive discards only the
// lower-priority soft constraints already seen (from earlier blocks, or earlier
// in this block) and never this block's own later soft constraints -- matching
// the class B example where 'disable soft x; soft x dist {5,8};' discards a
// preceding block's soft but keeps its own following distribution. The solver's
// ComputeDisabledSoft resolves these against the soft constraints; a directive
// that names a variable the block does not soft constrain discards nothing.
static void AddDisableSoftDirectives(const ClassMember* m,
                                     ConstraintBlock& block) {
  for (const auto& ref : m->constraint_disable_soft_refs) {
    ConstraintExpr ce;
    ce.kind = ConstraintKind::kDisableSoft;
    ce.var_name = std::string(ref.name);
    block.constraints.push_back(std::move(ce));
  }
}

// 18.5.13: build each captured soft constraint. The inner relation is
// translated exactly like a hard one but without folding the draw domain, then
// wrapped in a kSoft constraint. The solver seeds the inner so a satisfiable
// preference is honored, yet discards the soft (treating it as the value 1) and
// never fails the solve when the preference conflicts with the hard
// constraints. The inner is heap-owned in rc so the kSoft's raw pointer to it
// stays valid after the block is copied into the solver.
static void AddSoftConstraints(const ClassMember* m,
                               std::vector<RandInfo>& rands, RandomizeCtx& rc,
                               ConstraintBlock& block) {
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
}

// 18.5.13: a 'soft'-prefixed distribution wraps the dist alternative of the
// soft operand. The inner is built as an ordinary weighted-value (kDist)
// constraint, then wrapped in a kSoft: the solver seeds the distribution when
// it is honored and discards it (leaving its variable free) when it conflicts
// with the hard constraints.
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

// 18.5.4: build each captured uniqueness constraint as a kUnique solver
// constraint. Each range_list member that names an active rand variable is
// resolved to that solver variable; the solver then requires the named
// variables to hold pairwise-distinct values, enforces the no-randc and
// equivalent-type restrictions on the group, and treats a group of fewer than
// two known members as having no effect. A member the solver does not model as
// its own variable (e.g. an array slice, whose elements the scalar solver does
// not draw individually) is left out of the group, mirroring the lenient
// treatment of unknown references elsewhere in the translation.
static void AddUniqueConstraints(const ClassMember* m,
                                 std::vector<RandInfo>& rands,
                                 ConstraintBlock& block) {
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
}

// 18.5.9: lower each 'solve before_list before after_list' ordering into the
// solver's variable ordering. Only a simple local entry that resolves to an
// active rand variable participates; a qualified reference or an array.size()
// method -- which the scalar solver does not model as its own drawable variable
// -- is left out, mirroring the lenient treatment of unresolved references in
// the uniqueness lowering. The ordering only reweights the probability of the
// legal combinations and never removes a solution, so dropping an unresolved
// entry merely relaxes the order rather than losing a solution.
// The entries of one side of a solve...before list that resolve to an active
// rand variable the scalar solver draws.
static std::vector<std::string> ResolveOrderedNames(
    const std::vector<ConstraintSolveBeforeEntry>& entries,
    std::vector<RandInfo>& rands) {
  std::vector<std::string> names;
  for (const auto& e : entries)
    if (e.is_simple && FindRand(rands, e.name))
      names.push_back(std::string(e.name));
  return names;
}

static void AddSolveBeforeOrderings(const ClassMember* m,
                                    std::vector<RandInfo>& rands,
                                    ConstraintSolver& solver) {
  for (const auto& ref : m->constraint_solve_before_refs) {
    std::vector<std::string> before = ResolveOrderedNames(ref.before, rands);
    std::vector<std::string> after = ResolveOrderedNames(ref.after, rands);
    if (!before.empty() && !after.empty()) solver.AddSolveBefore(before, after);
  }
}

// 18.5.11: a random variable used as a function argument in a constraint
// establishes an implicit priority -- it is solved ahead of the variables of
// the constraint that consumes it, and its committed value is then read as a
// state variable when the function is called for the lower-priority set. For
// each hard relation, the rand variables appearing in a function-call argument
// position outrank the rand variables the relation uses directly, so that
// ordering is recorded for the solver's priority-layer pass. Only variables the
// solver models as its own drawable variable participate, mirroring the lenient
// treatment of unresolved references in the orderings above. A variable used
// directly is excluded from the lower set of the same relation when it also
// supplies an argument there, so a self-reference does not fabricate a
// degenerate cycle; a genuine cycle across relations (each uses the other as an
// argument) still forms and is rejected by SolveWith.
// The members of `names` the solver models as their own drawable variable,
// leaving out anything `excluded` already accounts for.
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
    CollectConstraintArgRefs(rel, /*in_arg=*/false, all_names, arg_names);
    std::vector<std::string> higher =
        FilterRandNames(arg_names, /*excluded=*/nullptr, rands);
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
  AddDisableSoftDirectives(m, block);
  AddSoftConstraints(m, rands, rc, block);
  AddSoftDistConstraints(m, rc, block);
  AddUniqueConstraints(m, rands, block);
  AddSolveBeforeOrderings(m, rands, solver);
  AddFunctionArgPriorities(m, rands, solver);

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
// Whether a constraint member has a body the solver can act on. 18.5.13.2: a
// block whose only body is a 'disable soft' directive still contributes -- it
// discards lower-priority soft constraints.
static bool ConstraintMemberContributes(const ClassMember* m) {
  return !m->constraint_exprs.empty() || !m->constraint_dist_refs.empty() ||
         !m->constraint_soft_exprs.empty() ||
         !m->constraint_soft_dist_refs.empty() ||
         !m->constraint_unique_refs.empty() ||
         !m->constraint_solve_before_refs.empty() ||
         !m->constraint_disable_soft_refs.empty();
}

// The constraint members one class level contributes: those with a body the
// solver can act on that a more-derived level has not already replaced
// (18.5.2).
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
    per_level.push_back(CollectLevelConstraints(lvl, replaced));
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

}  // namespace delta
