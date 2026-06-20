#include "elaborator/annex_f_vacuity_local_variables.h"

#include <algorithm>
#include <cstddef>
#include <memory>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

namespace delta {
namespace {

// §F.5 (page 1246): w-bar interchanges T and _|_; a letter in 2^P is unchanged.
Letter ComplementLetter(const Letter& letter) {
  switch (letter.kind) {
    case Letter::Kind::kTop:
      return LetterBottom();
    case Letter::Kind::kBottom:
      return LetterTop();
    case Letter::Kind::kAtomSet:
      return letter;
  }
  return letter;
}

// §F.5: w-bar, the letterwise complement of the whole word.
Word ComplementWord(const Word& word) {
  Word out;
  out.reserve(word.size());
  for (const Letter& letter : word) {
    out.push_back(ComplementLetter(letter));
  }
  return out;
}

// §F.5: w^{i.}, the word with its first i letters deleted (empty once i reaches
// the length of w).
Word Suffix(const Word& word, std::size_t i) {
  if (i >= word.size()) {
    return Word{};
  }
  return Word(word.begin() + static_cast<std::ptrdiff_t>(i), word.end());
}

// §F.5: w^{0,k}, the finite prefix w^0 w^1 ... w^k (the first k+1 letters).
Word PrefixInclusive(const Word& word, std::size_t k) {
  const std::size_t count = std::min(k + 1, word.size());
  return Word(word.begin(), word.begin() + static_cast<std::ptrdiff_t>(count));
}

// §F.5: the first i letters of w; the empty word when i = 0.
Word FirstLetters(const Word& word, std::size_t i) {
  const std::size_t count = std::min(i, word.size());
  return Word(word.begin(), word.begin() + static_cast<std::ptrdiff_t>(count));
}

// The least index at which a letter of the word satisfies b, or word.size() if
// no letter does. With b never satisfied this equals |w|, which is exactly the
// "for every 0 <= i < |w|, w^i |/= b" condition the abort/disable rules use.
std::size_t FirstSatisfyingIndex(const Word& word, const BooleanExpr& b) {
  for (std::size_t i = 0; i < word.size(); ++i) {
    if (LetterSatisfiesBoolean(word[i], b)) {
      return i;
    }
  }
  return word.size();
}

// A structural bound on how far a sequence can reach into a word, mirroring the
// bound §F.5.3.1 / §F.5.6.1 use for sizing the constant tails.
std::size_t SequenceReach(const SequenceExpr& seq) {
  switch (seq.kind) {
    case SequenceExpr::Kind::kBoolean:
    case SequenceExpr::Kind::kLocalVarSampling:
    case SequenceExpr::Kind::kNullRepeat:
      return 1;
    case SequenceExpr::Kind::kParen:
    case SequenceExpr::Kind::kFirstMatch:
    case SequenceExpr::Kind::kUnboundedRepeat:
    case SequenceExpr::Kind::kZeroOrMoreRepeat:
    case SequenceExpr::Kind::kLocalVarDecl:
      return seq.lhs ? SequenceReach(*seq.lhs) : 1;
    case SequenceExpr::Kind::kConcat:
    case SequenceExpr::Kind::kFusion:
      return (seq.lhs ? SequenceReach(*seq.lhs) : 0) +
             (seq.rhs ? SequenceReach(*seq.rhs) : 0);
    case SequenceExpr::Kind::kOr:
    case SequenceExpr::Kind::kIntersect:
      return std::max(seq.lhs ? SequenceReach(*seq.lhs) : 0,
                      seq.rhs ? SequenceReach(*seq.rhs) : 0);
    case SequenceExpr::Kind::kClock:
      return (seq.lhs ? SequenceReach(*seq.lhs) : 1) + 1;
  }
  return 1;
}

// A structural bound on how far a local-variable property can reach into a
// word; once a word's suffix lies entirely inside a constant tail this many
// letters past the explicit prefix, extending the tail cannot change the
// verdict.
std::size_t PropertyReach(const LvProperty& property) {
  switch (property.kind) {
    case LvProperty::Kind::kStrong:
    case LvProperty::Kind::kWeak:
      return property.sequence ? SequenceReach(*property.sequence) : 1;
    case LvProperty::Kind::kParen:
    case LvProperty::Kind::kNot:
    case LvProperty::Kind::kLocalVarDecl:
      return property.lhs ? PropertyReach(*property.lhs) : 1;
    case LvProperty::Kind::kImplication:
      return (property.sequence ? SequenceReach(*property.sequence) : 0) +
             (property.lhs ? PropertyReach(*property.lhs) : 0);
    case LvProperty::Kind::kOr:
    case LvProperty::Kind::kAnd:
      return std::max(property.lhs ? PropertyReach(*property.lhs) : 0,
                      property.rhs ? PropertyReach(*property.rhs) : 0);
    case LvProperty::Kind::kUntil:
      return (property.lhs ? PropertyReach(*property.lhs) : 0) +
             (property.rhs ? PropertyReach(*property.rhs) : 0) + 1;
    case LvProperty::Kind::kNexttime:
    case LvProperty::Kind::kAcceptOn:
      return (property.lhs ? PropertyReach(*property.lhs) : 0) + 1;
  }
  return 1;
}

// A finite materialization of a prefix followed by a constant tail (T^omega or
// _|_^omega), padded `reach` letters past the prefix plus a margin -- enough
// for the verdict to have stabilized for the finite properties this model
// handles.
Word PrefixWithTail(const Word& prefix, const Letter& tail, std::size_t reach) {
  Word out = prefix;
  const std::size_t pad = reach + 2;
  for (std::size_t i = 0; i < pad; ++i) {
    out.push_back(tail);
  }
  return out;
}

bool NonVacuous(const Word& word, const LvProperty& property,
                const LocalContext& context);

// §F.5.6.3 (inheriting §F.5.3.3): the abort/disable family shares one shape.
// w, L_0 |=^non OP(b) P iff w, L_0 |=^non P and one of: (1) for every
// 0 <= i < |w|, w^i |/= b; or (2) there is a b-free prefix x of w with
// x _|_^omega, L_0 |/= P or x T^omega, L_0 |/= P under §F.5.6.1's neutral
// satisfaction with locals. accept_on (b) P and disable iff (b) P both use it.
bool NonVacuousAbortShape(const Word& word, const BooleanExpr& boolean,
                          const LvProperty& operand,
                          const LocalContext& context) {
  if (!NonVacuous(word, operand, context)) {
    return false;
  }
  const std::size_t first_b = FirstSatisfyingIndex(word, boolean);
  // (1) No letter of w satisfies b.
  if (first_b == word.size()) {
    return true;
  }
  // (2) Some b-free prefix x leaves P unmet under one of the constant tails.
  // The prefixes with no b-letter are exactly those of length 0..first_b.
  const std::size_t reach = PropertyReach(operand);
  for (std::size_t len = 0; len <= first_b; ++len) {
    const Word prefix = FirstLetters(word, len);
    const Word bottom = PrefixWithTail(prefix, LetterBottom(), reach);
    const Word top = PrefixWithTail(prefix, LetterTop(), reach);
    if (!NeutrallySatisfiesWithLocals(bottom, operand, context) ||
        !NeutrallySatisfiesWithLocals(top, operand, context)) {
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
    case LvProperty::Kind::kImplication: {
      // §F.5.3.3: w, L_0 |=^non R |-> P iff there exists i >= 0 with w^{0,i}
      // tightly satisfying the trigger R -- on w itself, not w-bar -- under
      // some output context L_1, and w^{i.}, L_1 |=^non P. The four-way
      // relation yields the L_1 the antecedent produces; each is threaded into
      // P.
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
    case LvProperty::Kind::kOr:
      // §F.5.3.3: w, L_0 |=^non ( P1 or P2 ) iff w, L_0 |=^non P1 or
      // w, L_0 |=^non P2.
      return (property.lhs && NonVacuous(word, *property.lhs, context)) ||
             (property.rhs && NonVacuous(word, *property.rhs, context));
    case LvProperty::Kind::kAnd:
      // §F.5.3.3: w, L_0 |=^non ( P1 and P2 ) iff w, L_0 |=^non P1 or
      // w, L_0 |=^non P2. A conjunction is nonvacuous when either conjunct is.
      return (property.lhs && NonVacuous(word, *property.lhs, context)) ||
             (property.rhs && NonVacuous(word, *property.rhs, context));
    case LvProperty::Kind::kNexttime:
      // §F.5.3.3: w, L_0 |=^non ( nexttime P ) iff |w| > 0 and
      // w^{1.}, L_0 |=^non P.
      return !word.empty() && property.lhs &&
             NonVacuous(Suffix(word, 1), *property.lhs, context);
    case LvProperty::Kind::kUntil: {
      // §F.5.3.3: w, L_0 |=^non ( P1 until P2 ) iff there exists 0 <= i < |w|
      // with ( w^{i.}, L_0 |=^non P1 or w^{i.}, L_0 |=^non P2 ) and, for all
      // 0 <= j < i, w^{j.}, L_0 |= ( P1 and not P2 ) under §F.5.6.1's neutral
      // satisfaction with locals.
      if (!property.lhs || !property.rhs) {
        return false;
      }
      const std::shared_ptr<const LvProperty> guard =
          LvAnd(property.lhs, LvNot(property.rhs));
      for (std::size_t i = 0; i < word.size(); ++i) {
        const Word suffix_i = Suffix(word, i);
        if (!NonVacuous(suffix_i, *property.lhs, context) &&
            !NonVacuous(suffix_i, *property.rhs, context)) {
          continue;
        }
        bool prefix_holds = true;
        for (std::size_t j = 0; j < i; ++j) {
          if (!NeutrallySatisfiesWithLocals(Suffix(word, j), *guard, context)) {
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
