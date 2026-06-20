#include "elaborator/annex_f_vacuity_local_variables.h"

#include <algorithm>
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

}  // namespace

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
