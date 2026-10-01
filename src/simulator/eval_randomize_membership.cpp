#include <cstddef>
#include <cstdint>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/eval_member_path.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/evaluation.h"

namespace delta {

namespace {

// The value of a constant operand of a constraint, read as the type it was
// written in, so a signed operand holding a negative number stays negative.
int64_t ConstantOperand(const Expr* e, RandomizeCtx& rc) {
  auto cv = EvalExpr(e, rc.ctx, rc.arena);
  return cv.is_signed ? SignExtend(cv.ToUint64(), cv.width)
                      : static_cast<int64_t>(cv.ToUint64());
}

// The most values a set membership is enumerated into; a wider one is left
// to the kCustom path, which tries draws against the relation.
constexpr size_t kMaxEnumeratedMembers = 65536;

// §11.4.13: the `$` a range bound may be written as, its lowest or highest
// value, which the parser leaves as the identifier.
bool IsDollarBound(const Expr* e) {
  return e->kind == ExprKind::kIdentifier && e->text == "$";
}

// Adds the values `elem`, one item of an inside range list, names to `out`:
// a single value, or every value of a closed range of constants. Answers
// false for an item this path does not enumerate, one with a `$` bound, a
// tolerance or a span past kMaxEnumeratedMembers.
bool EnumerateInsideItem(const Expr* elem, RandomizeCtx& rc,
                         std::vector<int64_t>& out) {
  bool is_range = elem->kind == ExprKind::kSelect && elem->index != nullptr &&
                  elem->index_end != nullptr;
  // §11.4.13: an unpacked array adds each of its elements to the set.
  std::vector<Logic4Vec> members;
  if (!is_range && CollectUnpackedSetMembers(elem, rc.ctx, members)) {
    for (const Logic4Vec& m : members) {
      out.push_back(m.is_signed ? SignExtend(m.ToUint64(), m.width)
                                : static_cast<int64_t>(m.ToUint64()));
    }
    return out.size() <= kMaxEnumeratedMembers;
  }
  if (!is_range) {
    out.push_back(ConstantOperand(elem, rc));
    return true;
  }
  if (elem->op == TokenKind::kPlusSlashMinus ||
      elem->op == TokenKind::kPlusPercentMinus || IsDollarBound(elem->index) ||
      IsDollarBound(elem->index_end)) {
    return false;
  }
  int64_t lo = ConstantOperand(elem->index, rc);
  int64_t hi = ConstantOperand(elem->index_end, rc);
  if (lo > hi) return true;
  if (static_cast<uint64_t>(hi - lo) >= kMaxEnumeratedMembers) return false;
  for (int64_t v = lo; v <= hi; ++v) out.push_back(v);
  return out.size() <= kMaxEnumeratedMembers;
}

}  // namespace

bool EnumerateInsideItems(const std::vector<Expr*>& elements,
                          ClassObject* owner, RandomizeCtx& rc,
                          std::vector<int64_t>& out) {
  ConstraintEvalScope scope(owner, rc.ctx);
  for (const Expr* elem : elements) {
    if (!EnumerateInsideItem(elem, rc, out)) return false;
  }
  return true;
}

// 18.5.4: `x inside { ... }` over a rand variable and items free of random
// variables is a set membership the solver draws a member of, which a
// domain as wide as an int's needs: a draw tried against the relation
// finds one of a few members among 2^32 values as good as never. Fills
// `out` and answers true; any other shape answers false for the kCustom
// path.
bool TrySetMembershipConstraint(const Expr* rel, std::vector<RandInfo>& rands,
                                RandomizeCtx& rc, ConstraintExpr& out) {
  if (rel == nullptr || rel->kind != ExprKind::kInside || rel->lhs == nullptr ||
      rel->lhs->kind != ExprKind::kIdentifier ||
      FindRand(rands, rel->lhs->text) == nullptr ||
      AnyRefsRandVar(rel->elements, rands)) {
    return false;
  }
  // §18.4.1 with §11.4.13: a real variable inside a range of reals lies in
  // the closed interval between its bounds, which the solver draws from as
  // the two comparisons bound it; its values are no set to enumerate.
  if (FindRand(rands, rel->lhs->text)->var.is_real) {
    const Expr* range = rel->elements.size() == 1 ? rel->elements[0] : nullptr;
    if (range == nullptr || range->kind != ExprKind::kSelect ||
        range->index == nullptr || range->index_end == nullptr ||
        range->op == TokenKind::kPlusSlashMinus ||
        range->op == TokenKind::kPlusPercentMinus ||
        IsDollarBound(range->index) || IsDollarBound(range->index_end)) {
      return false;
    }
    auto compare = [&](TokenKind op, Expr* bound) {
      auto* e = rc.arena.Create<Expr>();
      e->kind = ExprKind::kBinary;
      e->range = rel->range;
      e->op = op;
      e->lhs = rel->lhs;
      e->rhs = bound;
      return e;
    };
    auto* both = rc.arena.Create<Expr>();
    both->kind = ExprKind::kBinary;
    both->range = rel->range;
    both->op = TokenKind::kAmpAmp;
    both->lhs = compare(TokenKind::kGtEq, range->index);
    both->rhs = compare(TokenKind::kLtEq, range->index_end);
    return TryConjunctionConstraint(both, rands, rc, out, /*fold=*/true);
  }
  std::vector<int64_t> values;
  if (!EnumerateInsideItems(rel->elements, rc.obj, rc, values)) return false;
  out.kind = ConstraintKind::kSetMembership;
  out.var_name = std::string(rel->lhs->text);
  out.set_values = std::move(values);
  out.ref_vars.push_back(out.var_name);
  return true;
}

namespace {

// A decimal literal of `value`, standing where `like` does.
Expr* BitLiteral(uint32_t value, const Expr* like, Arena& arena) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->range = like->range;
  e->int_val = value;
  std::string text = std::to_string(value);
  e->text = {arena.AllocString(text.data(), text.size()), text.size()};
  return e;
}

// §18.4: the variable of its own a rand member of a rand unpacked structure,
// `h1.addr`, is solved as; null for any other expression.
Expr* StructMemberVariable(const Expr* n, std::vector<RandInfo>& rands,
                           Arena& arena) {
  if (n->kind != ExprKind::kMemberAccess || n->lhs == nullptr ||
      n->rhs == nullptr || n->lhs->kind != ExprKind::kIdentifier ||
      n->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  std::string member =
      std::string(n->lhs->text) + "." + std::string(n->rhs->text);
  return FindRand(rands, member) != nullptr ? IdentifierExpr(member, n, arena)
                                            : nullptr;
}

// §18.4: the part-select, `p[7:4]`, of the bits a member of a rand packed
// structure, `p.hi`, occupies; null for any other expression.
Expr* PackedMemberSelect(const Expr* n, std::vector<RandInfo>& rands,
                         RandomizeCtx& rc) {
  PackedMemberBits bits;
  if (n->kind != ExprKind::kMemberAccess ||
      !PropertyPackedMemberBits(n, rc.obj, rc.ctx, bits) || bits.width == 0 ||
      FindRand(rands, bits.prop) == nullptr) {
    return nullptr;
  }
  auto* select = rc.arena.Create<Expr>();
  select->kind = ExprKind::kSelect;
  select->range = n->range;
  select->base = IdentifierExpr(bits.prop, n, rc.arena);
  select->index = BitLiteral(bits.offset + bits.width - 1, n, rc.arena);
  select->index_end = BitLiteral(bits.offset, n, rc.arena);
  return select;
}

}  // namespace

const Expr* PackedMembersAsSelects(const Expr* rel,
                                   std::vector<RandInfo>& rands,
                                   RandomizeCtx& rc) {
  return RewriteExpr(
      rel,
      [&](const Expr* n) -> Expr* {
        if (Expr* member = StructMemberVariable(n, rands, rc.arena))
          return member;
        return PackedMemberSelect(n, rands, rc);
      },
      rc.arena);
}

bool TryImplicationConstraint(const Expr* rel, std::vector<RandInfo>& rands,
                              RandomizeCtx& rc, ConstraintExpr& out) {
  if (rel == nullptr || rel->kind != ExprKind::kBinary ||
      rel->op != TokenKind::kArrow || rel->lhs == nullptr ||
      rel->rhs == nullptr) {
    return false;
  }
  // The consequent's bounds hold only where the antecedent does, so none of
  // them folds the variable's domain. A consequent the solver would try as
  // a whole is left to be tried with its antecedent, unless it derives one
  // variable from the others, which the solver's repair of the implication
  // applies where the antecedent holds (18.5.7.1).
  ConstraintExpr consequent =
      TranslateRelation(rel->rhs, rands, rc, /*fold=*/false);
  if (consequent.kind == ConstraintKind::kCustom && !consequent.derive_fn)
    return false;
  std::vector<std::string> names;
  names.reserve(rands.size());
  for (const auto& ri : rands) names.push_back(ri.name);
  out.kind = ConstraintKind::kImplication;
  out.ref_vars = names;
  out.cond_fn = [antecedent = rel->lhs, names,
                 &rc](const std::unordered_map<std::string, int64_t>& vals) {
    return EvalCustomRelation(antecedent, names, rc, vals);
  };
  out.sub_constraints.push_back(std::move(consequent));
  return true;
}

ConstraintExpr SoftImplication(const Expr* rel, std::vector<RandInfo>& rands,
                               RandomizeCtx& rc) {
  ConstraintExpr consequent =
      TranslateRelation(rel->rhs, rands, rc, /*fold=*/false);
  std::vector<std::string> names;
  names.reserve(rands.size());
  for (const auto& ri : rands) names.push_back(ri.name);
  ConstraintExpr out;
  out.kind = ConstraintKind::kImplication;
  // 18.5.13.2: the antecedent only gates the soft constraint, so the
  // variables the soft constraint directly references, which a 'disable
  // soft' directive discards it by, are the consequent's alone.
  out.ref_vars = consequent.ref_vars;
  out.cond_fn = [antecedent = rel->lhs, names,
                 &rc](const std::unordered_map<std::string, int64_t>& vals) {
    return EvalCustomRelation(antecedent, names, rc, vals);
  };
  out.sub_constraints.push_back(std::move(consequent));
  return out;
}

bool TryConjunctionConstraint(const Expr* rel, std::vector<RandInfo>& rands,
                              RandomizeCtx& rc, ConstraintExpr& out,
                              bool fold) {
  if (rel == nullptr || rel->kind != ExprKind::kBinary ||
      rel->op != TokenKind::kAmpAmp || rel->lhs == nullptr ||
      rel->rhs == nullptr) {
    return false;
  }
  out.kind = ConstraintKind::kImplication;
  for (const auto& ri : rands) out.ref_vars.push_back(ri.name);
  out.cond_fn = [](const std::unordered_map<std::string, int64_t>&) {
    return true;
  };
  out.sub_constraints.push_back(TranslateRelation(rel->lhs, rands, rc, fold));
  out.sub_constraints.push_back(TranslateRelation(rel->rhs, rands, rc, fold));
  return true;
}

}  // namespace delta
