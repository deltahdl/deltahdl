#include "elaborator/annex_f_vacuity_local_variables.h"

#include <cstddef>
#include <memory>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"
#include "elaborator/annex_f_word_ops_internal.h"

namespace delta {
namespace {

bool NonVacuous(const Word& word, const LvProperty& property,
                const LocalContext& context);

// §F.5.6.3 (inheriting §F.5.3.3) abort/disable shape, specialized for the
// local-variable property layer: non-vacuity and neutral satisfaction thread a
// LocalContext through both policies.
bool NonVacuousAbortShape(const Word& word, const BooleanExpr& boolean,
                          const LvProperty& operand,
                          const LocalContext& context) {
  return ::delta::NonVacuousAbortShape(
      word, boolean, operand,
      [&context](const Word& w, const LvProperty& p) {
        return NonVacuous(w, p, context);
      },
      [&context](const Word& w, const LvProperty& p) {
        return NeutrallySatisfiesWithLocals(w, p, context);
      });
}

// §F.5.3.3: w, L_0 |=^non R |-> P iff there exists i >= 0 with w^{0,i}
// tightly satisfying the trigger R -- on w itself, not w-bar -- under
// some output context L_1, and w^{i.}, L_1 |=^non P. The four-way
// relation yields the L_1 the antecedent produces; each is threaded into
// P.
bool NonVacuousImplication(const Word& word, const LvProperty& property,
                           const LocalContext& context) {
  if (!property.sequence || !property.lhs) {
    return false;
  }
  for (std::size_t i = 0; i < word.size(); ++i) {
    for (const LocalContext& out : TightSatisfactionOutputs(
             PrefixInclusive(word, i), *property.sequence, context)) {
      if (NonVacuous(Suffix(word, i), *property.lhs, out)) {
        return true;
      }
    }
  }
  return false;
}

// §F.5.3.3: w, L_0 |=^non ( P1 until P2 ) iff there exists 0 <= i < |w|
// with ( w^{i.}, L_0 |=^non P1 or w^{i.}, L_0 |=^non P2 ) and, for all
// 0 <= j < i, w^{j.}, L_0 |= ( P1 and not P2 ) under §F.5.6.1's neutral
// satisfaction with locals.
bool NonVacuousUntil(const Word& word, const LvProperty& property,
                     const LocalContext& context) {
  if (!property.lhs || !property.rhs) {
    return false;
  }
  const std::shared_ptr<const LvProperty> kGuard =
      LvAnd(property.lhs, LvNot(property.rhs));
  for (std::size_t i = 0; i < word.size(); ++i) {
    const Word kSuffixI = Suffix(word, i);
    if (!NonVacuous(kSuffixI, *property.lhs, context) &&
        !NonVacuous(kSuffixI, *property.rhs, context)) {
      continue;
    }
    bool prefix_holds = true;
    for (std::size_t j = 0; j < i; ++j) {
      if (!NeutrallySatisfiesWithLocals(Suffix(word, j), *kGuard, context)) {
        prefix_holds = false;
        break;
      }
    }
    if (prefix_holds) {
      return true;
    }
  }
  return false;
}

bool NonVacuous(const Word& word, const LvProperty& property,
                const LocalContext& context) {
  switch (property.kind) {
    case LvProperty::Kind::kStrong:
    case LvProperty::Kind::kWeak:
      // §F.5.3.3 base: w, L_0 |=^non strong(R) and weak(R) hold for every w;
      // the context plays no role.
      return true;
    case LvProperty::Kind::kLocalVarDecl:
      // §F.5.6.3: w, L_0 |=^non ( t v ; P ) iff w, L_0\v |=^non P. The declared
      // name is stripped from the context the body sees -- the only rule this
      // subclause states explicitly.
      return property.lhs &&
             NonVacuous(word, *property.lhs,
                        RemoveName(context, property.local_var_name));
    case LvProperty::Kind::kParen:
      // §F.5.3.3: w, L_0 |=^non ( P ) iff w, L_0 |=^non P.
      return property.lhs && NonVacuous(word, *property.lhs, context);
    case LvProperty::Kind::kNot:
      // §F.5.3.3: w, L_0 |=^non not P iff w-bar, L_0 |=^non P.
      return property.lhs &&
             NonVacuous(ComplementWord(word), *property.lhs, context);
    case LvProperty::Kind::kImplication:
      return NonVacuousImplication(word, property, context);
    case LvProperty::Kind::kOr:
    case LvProperty::Kind::kAnd:
      // §F.5.3.3: w, L_0 |=^non ( P1 or P2 ) iff w, L_0 |=^non P1 or
      // w, L_0 |=^non P2; and w, L_0 |=^non ( P1 and P2 ) holds when either
      // conjunct is nonvacuous. Both reduce to the same disjunctive test.
      return (property.lhs && NonVacuous(word, *property.lhs, context)) ||
             (property.rhs && NonVacuous(word, *property.rhs, context));
    case LvProperty::Kind::kNexttime:
      // §F.5.3.3: w, L_0 |=^non ( nexttime P ) iff |w| > 0 and
      // w^{1.}, L_0 |=^non P.
      return !word.empty() && property.lhs &&
             NonVacuous(Suffix(word, 1), *property.lhs, context);
    case LvProperty::Kind::kUntil:
      return NonVacuousUntil(word, property, context);
    case LvProperty::Kind::kAcceptOn:
      // §F.5.3.3: w, L_0 |=^non ( accept_on (b) P ) shares the abort shape.
      return property.boolean && property.lhs &&
             NonVacuousAbortShape(word, *property.boolean, *property.lhs,
                                  context);
  }
  return false;
}

// The guard the always and eventually rules place on the letters before their
// witness: w, L_0 |= P, or w, L_0 |= not P, which is w-bar, L_0 |/= P by the
// negation rule of §F.5.6.1.
bool GuardHolds(const Word& word, const LvProperty& p, bool negated,
                const LocalContext& context) {
  if (negated) {
    return !NeutrallySatisfiesWithLocals(ComplementWord(word), p, context);
  }
  return NeutrallySatisfiesWithLocals(word, p, context);
}

// The indices a witness may take: first through last inclusive.
struct IndexRange {
  std::size_t first = 0;
  std::size_t last = 0;
};

// §F.5.3.3's shape for the always and eventually rules of the derived
// operators, with the context threaded: some index i in the range has
// w^{i.}, L_0 |=^non P, and every j from the first index up to i has
// w^{j.}, L_0 |= P for the always rules or w^{j.}, L_0 |= not P for the
// eventually rules.
bool NonVacuousAfterGuardedPrefix(const Word& word, const LvProperty& p,
                                  bool guard_negated, IndexRange range,
                                  const LocalContext& context) {
  for (std::size_t i = range.first; i <= range.last; ++i) {
    if (!NonVacuous(Suffix(word, i), p, context)) {
      continue;
    }
    bool guarded = true;
    for (std::size_t j = range.first; j < i; ++j) {
      if (!GuardHolds(Suffix(word, j), p, guard_negated, context)) {
        guarded = false;
        break;
      }
    }
    if (guarded) {
      return true;
    }
  }
  return false;
}

// The range 0 .. |w|-1 of the unbounded rules, empty on the empty word.
bool NonVacuousAfterGuardedPrefixOnTheWord(const Word& word,
                                           const LvProperty& p,
                                           bool guard_negated,
                                           const LocalContext& context) {
  if (word.empty()) {
    return false;
  }
  return NonVacuousAfterGuardedPrefix(word, p, guard_negated,
                                      IndexRange{0, word.size() - 1}, context);
}

}  // namespace

bool NonVacuouslyEvaluatesIffWithLocals(const Word& word, const LvProperty& p1,
                                        const LvProperty& p2,
                                        const LocalContext& context) {
  // §F.5.3.3: either operand nonvacuous.
  return NonVacuous(word, p1, context) || NonVacuous(word, p2, context);
}

bool NonVacuouslyEvaluatesImpliesWithLocals(const Word& word,
                                            const LvProperty& p1,
                                            const LvProperty& p2,
                                            const LocalContext& context) {
  // §F.5.3.3: the antecedent holds and is nonvacuous, and the consequent is
  // nonvacuous.
  return NeutrallySatisfiesWithLocals(word, p1, context) &&
         NonVacuous(word, p1, context) && NonVacuous(word, p2, context);
}

bool NonVacuouslyEvaluatesSUntilWithLocals(const Word& word,
                                           const LvProperty& p1,
                                           const LvProperty& p2,
                                           const LocalContext& context) {
  // §F.5.3.3: the rule of the until, stated again for s_until.
  return NonVacuousUntil(word,
                         *LvUntil(std::make_shared<LvProperty>(p1),
                                  std::make_shared<LvProperty>(p2)),
                         context);
}

bool NonVacuouslyEvaluatesAlwaysWithLocals(const Word& word,
                                           const LvProperty& p,
                                           const LocalContext& context) {
  // §F.5.3.3: some 0 <= i < |w| from which P is nonvacuous, P holding from
  // every earlier letter.
  return NonVacuousAfterGuardedPrefixOnTheWord(word, p, false, context);
}

bool NonVacuouslyEvaluatesAlwaysRangeWithLocals(const Word& word,
                                                const LvProperty& p,
                                                unsigned int m, unsigned int n,
                                                const LocalContext& context) {
  // §F.5.3.3: some m <= i <= n from which P is nonvacuous, P holding from
  // every letter m through i-1.
  return NonVacuousAfterGuardedPrefix(word, p, false, IndexRange{m, n},
                                      context);
}

bool NonVacuouslyEvaluatesSAlwaysRangeWithLocals(const Word& word,
                                                 const LvProperty& p,
                                                 unsigned int m, unsigned int n,
                                                 const LocalContext& context) {
  // §F.5.3.3: the rule of always [m:n], stated again for s_always [m:n].
  return NonVacuouslyEvaluatesAlwaysRangeWithLocals(word, p, m, n, context);
}

bool NonVacuouslyEvaluatesSEventuallyWithLocals(const Word& word,
                                                const LvProperty& p,
                                                const LocalContext& context) {
  // §F.5.3.3: some 0 <= i < |w| from which P is nonvacuous, not P holding
  // from every earlier letter.
  return NonVacuousAfterGuardedPrefixOnTheWord(word, p, true, context);
}

bool NonVacuouslyEvaluatesEventuallyRangeWithLocals(
    const Word& word, const LvProperty& p, unsigned int m, unsigned int n,
    const LocalContext& context) {
  // §F.5.3.3: some m <= i <= n from which P is nonvacuous, not P holding from
  // every letter m through i-1.
  return NonVacuousAfterGuardedPrefix(word, p, true, IndexRange{m, n}, context);
}

bool NonVacuouslyEvaluatesSEventuallyRangeWithLocals(
    const Word& word, const LvProperty& p, unsigned int m, unsigned int n,
    const LocalContext& context) {
  // §F.5.3.3: the rule of eventually [m:n], stated again for
  // s_eventually [m:n].
  return NonVacuouslyEvaluatesEventuallyRangeWithLocals(word, p, m, n, context);
}

bool NonVacuouslyEvaluatesRejectOnWithLocals(const Word& word,
                                             const BooleanExpr& b,
                                             const LvProperty& p,
                                             const LocalContext& context) {
  // §F.5.3.3: reject_on (b) P shares the abort/disable shape.
  return NonVacuousAbortShape(word, b, p, context);
}

bool NonVacuouslyEvaluatesWithLocals(const Word& word,
                                     const LvProperty& property,
                                     const LocalContext& context) {
  return NonVacuous(word, property, context);
}

bool NonVacuouslyEvaluatesWithLocals(const Word& word,
                                     const LvProperty& property) {
  // §F.5.6.3 / §F.5.6.1: start the recursion from no live local variables.
  return NonVacuous(word, property, LocalContext{});
}

bool NonVacuouslyEvaluatesTopLevelWithLocals(const Word& word,
                                             const LvTopLevelProperty& top,
                                             const LocalContext& context) {
  switch (top.kind) {
    case LvTopLevelProperty::Kind::kProperty:
      // §F.5.3.3 applies to the property directly.
      return top.property && NonVacuous(word, *top.property, context);
    case LvTopLevelProperty::Kind::kDisableIff:
      // §F.5.3.3: w, L_0 |=^non disable iff (b) P uses the same shape as
      // accept_on.
      return top.disable_condition && top.property &&
             NonVacuousAbortShape(word, *top.disable_condition, *top.property,
                                  context);
    case LvTopLevelProperty::Kind::kParen:
      // A parenthesized top-level property is transparent, as for ( P ).
      return top.inner &&
             NonVacuouslyEvaluatesTopLevelWithLocals(word, *top.inner, context);
    case LvTopLevelProperty::Kind::kLocalVarDecl:
      // §F.5.6.3: w, L_0 |=^non ( t v ; T ) iff w, L_0\v |=^non T.
      return top.inner &&
             NonVacuouslyEvaluatesTopLevelWithLocals(
                 word, *top.inner, RemoveName(context, top.local_var_name));
  }
  return false;
}

bool SatisfiesNonVacuouslyWithLocals(const Word& word,
                                     const LvProperty& property,
                                     const LocalContext& context) {
  // §F.5.6.3 (inheriting §F.5.3.3): w satisfies P nonvacuously iff w, L_0 |= P
  // and w, L_0 |=^non P.
  return NeutrallySatisfiesWithLocals(word, property, context) &&
         NonVacuouslyEvaluatesWithLocals(word, property, context);
}

bool SatisfiesTopLevelNonVacuouslyWithLocals(const Word& word,
                                             const LvTopLevelProperty& top,
                                             const LocalContext& context) {
  // §F.5.6.3 at the top level: neutral satisfaction with locals together with
  // non-vacuity.
  return NeutrallySatisfiesTopLevelWithLocals(word, top, context) &&
         NonVacuouslyEvaluatesTopLevelWithLocals(word, top, context);
}

}  // namespace delta
