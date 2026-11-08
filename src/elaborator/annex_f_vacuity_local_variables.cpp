#include "elaborator/annex_f_vacuity_local_variables.h"

#include <cstddef>
#include <memory>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"
#include "elaborator/annex_f_word_ops_internal.h"

namespace delta {
namespace {

bool NonVacuous(const Word& word, const LvProperty& property,
                const LocalContext& context);

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
      return true;
    case LvProperty::Kind::kLocalVarDecl:
      return property.lhs &&
             NonVacuous(word, *property.lhs,
                        RemoveName(context, property.local_var_name));
    case LvProperty::Kind::kParen:
      return property.lhs && NonVacuous(word, *property.lhs, context);
    case LvProperty::Kind::kNot:
      return property.lhs &&
             NonVacuous(ComplementWord(word), *property.lhs, context);
    case LvProperty::Kind::kImplication:
      return NonVacuousImplication(word, property, context);
    case LvProperty::Kind::kOr:
    case LvProperty::Kind::kAnd:
      return (property.lhs && NonVacuous(word, *property.lhs, context)) ||
             (property.rhs && NonVacuous(word, *property.rhs, context));
    case LvProperty::Kind::kNexttime:
      return !word.empty() && property.lhs &&
             NonVacuous(Suffix(word, 1), *property.lhs, context);
    case LvProperty::Kind::kUntil:
      return NonVacuousUntil(word, property, context);
    case LvProperty::Kind::kAcceptOn:
      return property.boolean && property.lhs &&
             NonVacuousAbortShape(word, *property.boolean, *property.lhs,
                                  context);
  }
  return false;
}

bool GuardHolds(const Word& word, const LvProperty& p, bool negated,
                const LocalContext& context) {
  if (negated) {
    return !NeutrallySatisfiesWithLocals(ComplementWord(word), p, context);
  }
  return NeutrallySatisfiesWithLocals(word, p, context);
}

struct IndexRange {
  std::size_t first = 0;
  std::size_t last = 0;
};

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
  return NonVacuous(word, p1, context) || NonVacuous(word, p2, context);
}

bool NonVacuouslyEvaluatesImpliesWithLocals(const Word& word,
                                            const LvProperty& p1,
                                            const LvProperty& p2,
                                            const LocalContext& context) {
  return NeutrallySatisfiesWithLocals(word, p1, context) &&
         NonVacuous(word, p1, context) && NonVacuous(word, p2, context);
}

bool NonVacuouslyEvaluatesSUntilWithLocals(const Word& word,
                                           const LvProperty& p1,
                                           const LvProperty& p2,
                                           const LocalContext& context) {
  return NonVacuousUntil(word,
                         *LvUntil(std::make_shared<LvProperty>(p1),
                                  std::make_shared<LvProperty>(p2)),
                         context);
}

bool NonVacuouslyEvaluatesAlwaysWithLocals(const Word& word,
                                           const LvProperty& p,
                                           const LocalContext& context) {
  return NonVacuousAfterGuardedPrefixOnTheWord(word, p, false, context);
}

bool NonVacuouslyEvaluatesAlwaysRangeWithLocals(const Word& word,
                                                const LvProperty& p,
                                                unsigned int m, unsigned int n,
                                                const LocalContext& context) {
  return NonVacuousAfterGuardedPrefix(word, p, false, IndexRange{m, n},
                                      context);
}

bool NonVacuouslyEvaluatesSAlwaysRangeWithLocals(const Word& word,
                                                 const LvProperty& p,
                                                 unsigned int m, unsigned int n,
                                                 const LocalContext& context) {
  return NonVacuouslyEvaluatesAlwaysRangeWithLocals(word, p, m, n, context);
}

bool NonVacuouslyEvaluatesSEventuallyWithLocals(const Word& word,
                                                const LvProperty& p,
                                                const LocalContext& context) {
  return NonVacuousAfterGuardedPrefixOnTheWord(word, p, true, context);
}

bool NonVacuouslyEvaluatesEventuallyRangeWithLocals(
    const Word& word, const LvProperty& p, unsigned int m, unsigned int n,
    const LocalContext& context) {
  return NonVacuousAfterGuardedPrefix(word, p, true, IndexRange{m, n}, context);
}

bool NonVacuouslyEvaluatesSEventuallyRangeWithLocals(
    const Word& word, const LvProperty& p, unsigned int m, unsigned int n,
    const LocalContext& context) {
  return NonVacuouslyEvaluatesEventuallyRangeWithLocals(word, p, m, n, context);
}

bool NonVacuouslyEvaluatesRejectOnWithLocals(const Word& word,
                                             const BooleanExpr& b,
                                             const LvProperty& p,
                                             const LocalContext& context) {
  return NonVacuousAbortShape(word, b, p, context);
}

bool NonVacuouslyEvaluatesWithLocals(const Word& word,
                                     const LvProperty& property,
                                     const LocalContext& context) {
  return NonVacuous(word, property, context);
}

bool NonVacuouslyEvaluatesWithLocals(const Word& word,
                                     const LvProperty& property) {
  return NonVacuous(word, property, LocalContext{});
}

bool NonVacuouslyEvaluatesTopLevelWithLocals(const Word& word,
                                             const LvTopLevelProperty& top,
                                             const LocalContext& context) {
  switch (top.kind) {
    case LvTopLevelProperty::Kind::kProperty:
      return top.property && NonVacuous(word, *top.property, context);
    case LvTopLevelProperty::Kind::kDisableIff:
      return top.disable_condition && top.property &&
             NonVacuousAbortShape(word, *top.disable_condition, *top.property,
                                  context);
    case LvTopLevelProperty::Kind::kParen:
      return top.inner &&
             NonVacuouslyEvaluatesTopLevelWithLocals(word, *top.inner, context);
    case LvTopLevelProperty::Kind::kLocalVarDecl:
      return top.inner &&
             NonVacuouslyEvaluatesTopLevelWithLocals(
                 word, *top.inner, RemoveName(context, top.local_var_name));
  }
  return false;
}

bool SatisfiesNonVacuouslyWithLocals(const Word& word,
                                     const LvProperty& property,
                                     const LocalContext& context) {
  return NeutrallySatisfiesWithLocals(word, property, context) &&
         NonVacuouslyEvaluatesWithLocals(word, property, context);
}

bool SatisfiesTopLevelNonVacuouslyWithLocals(const Word& word,
                                             const LvTopLevelProperty& top,
                                             const LocalContext& context) {
  return NeutrallySatisfiesTopLevelWithLocals(word, top, context) &&
         NonVacuouslyEvaluatesTopLevelWithLocals(word, top, context);
}

}  // namespace delta
