#include "elaborator/annex_f_neutral_satisfaction.h"

#include <cstddef>
#include <memory>
#include <utility>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_word_ops_internal.h"

namespace delta {

std::shared_ptr<const PropertyExpr> PropStrong(
    std::shared_ptr<const SequenceExpr> r) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kStrong;
  p->sequence = std::move(r);
  return p;
}

std::shared_ptr<const PropertyExpr> PropWeak(
    std::shared_ptr<const SequenceExpr> r) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kWeak;
  p->sequence = std::move(r);
  return p;
}

std::shared_ptr<const PropertyExpr> PropParen(
    std::shared_ptr<const PropertyExpr> inner) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kParen;
  p->lhs = std::move(inner);
  return p;
}

std::shared_ptr<const PropertyExpr> PropNot(
    std::shared_ptr<const PropertyExpr> inner) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kNot;
  p->lhs = std::move(inner);
  return p;
}

std::shared_ptr<const PropertyExpr> PropImplication(
    std::shared_ptr<const SequenceExpr> antecedent,
    std::shared_ptr<const PropertyExpr> consequent) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kImplication;
  p->sequence = std::move(antecedent);
  p->lhs = std::move(consequent);
  return p;
}

std::shared_ptr<const PropertyExpr> PropOr(
    std::shared_ptr<const PropertyExpr> a,
    std::shared_ptr<const PropertyExpr> b) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kOr;
  p->lhs = std::move(a);
  p->rhs = std::move(b);
  return p;
}

std::shared_ptr<const PropertyExpr> PropAnd(
    std::shared_ptr<const PropertyExpr> a,
    std::shared_ptr<const PropertyExpr> b) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kAnd;
  p->lhs = std::move(a);
  p->rhs = std::move(b);
  return p;
}

std::shared_ptr<const PropertyExpr> PropNexttime(
    std::shared_ptr<const PropertyExpr> inner) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kNexttime;
  p->lhs = std::move(inner);
  return p;
}

std::shared_ptr<const PropertyExpr> PropUntil(
    std::shared_ptr<const PropertyExpr> a,
    std::shared_ptr<const PropertyExpr> b) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kUntil;
  p->lhs = std::move(a);
  p->rhs = std::move(b);
  return p;
}

std::shared_ptr<const PropertyExpr> PropAcceptOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> inner) {
  auto p = std::make_shared<PropertyExpr>();
  p->kind = PropertyExpr::Kind::kAcceptOn;
  p->boolean = std::move(b);
  p->lhs = std::move(inner);
  return p;
}

std::shared_ptr<const TopLevelProperty> TopProperty(
    std::shared_ptr<const PropertyExpr> p) {
  auto t = std::make_shared<TopLevelProperty>();
  t->kind = TopLevelProperty::Kind::kProperty;
  t->property = std::move(p);
  return t;
}

std::shared_ptr<const TopLevelProperty> TopDisableIff(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> p) {
  auto t = std::make_shared<TopLevelProperty>();
  t->kind = TopLevelProperty::Kind::kDisableIff;
  t->disable_condition = std::move(b);
  t->property = std::move(p);
  return t;
}

std::shared_ptr<const TopLevelProperty> TopParen(
    std::shared_ptr<const TopLevelProperty> inner) {
  auto t = std::make_shared<TopLevelProperty>();
  t->kind = TopLevelProperty::Kind::kParen;
  t->inner = std::move(inner);
  return t;
}

std::shared_ptr<const ClockedTopLevelProperty> ClockedTopProperty(
    std::shared_ptr<const ClockedProperty> q) {
  auto u = std::make_shared<ClockedTopLevelProperty>();
  u->kind = ClockedTopLevelProperty::Kind::kProperty;
  u->property = std::move(q);
  return u;
}

std::shared_ptr<const ClockedTopLevelProperty> ClockedTopDisableIff(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> q) {
  auto u = std::make_shared<ClockedTopLevelProperty>();
  u->kind = ClockedTopLevelProperty::Kind::kDisableIff;
  u->disable_condition = std::move(b);
  u->property = std::move(q);
  return u;
}

std::shared_ptr<const ClockedTopLevelProperty> ClockedTopParen(
    std::shared_ptr<const ClockedTopLevelProperty> inner) {
  auto u = std::make_shared<ClockedTopLevelProperty>();
  u->kind = ClockedTopLevelProperty::Kind::kParen;
  u->inner = std::move(inner);
  return u;
}

std::shared_ptr<const AssertionStatement> AssertionWithClock(
    AssertionStatement::Activation activation, AssertionStatement::Role role,
    std::shared_ptr<const BooleanExpr> clock,
    std::shared_ptr<const TopLevelProperty> top) {
  auto a = std::make_shared<AssertionStatement>();
  a->activation = activation;
  a->role = role;
  a->form = AssertionStatement::Form::kExplicitClock;
  a->clock = std::move(clock);
  a->top = std::move(top);
  return a;
}

std::shared_ptr<const AssertionStatement> AssertionWithClockedTop(
    AssertionStatement::Activation activation, AssertionStatement::Role role,
    std::shared_ptr<const ClockedTopLevelProperty> clocked_top) {
  auto a = std::make_shared<AssertionStatement>();
  a->activation = activation;
  a->role = role;
  a->form = AssertionStatement::Form::kClockedTop;
  a->clocked_top = std::move(clocked_top);
  return a;
}

namespace {

bool StrongHolds(const Word& word, const SequenceExpr& seq) {
  for (std::size_t j = 0; j < word.size(); ++j) {
    if (TightlySatisfies(PrefixInclusive(word, j), seq)) {
      return true;
    }
  }
  return false;
}

bool Satisfies(const Word& word, const PropertyExpr& property);

bool WeakHolds(const Word& word, const SequenceExpr& seq) {
  const std::size_t kReach = SequenceReach(seq);
  for (std::size_t j = 0; j < word.size(); ++j) {
    const Word kCompleted =
        PrefixWithTail(PrefixInclusive(word, j), LetterTop(), kReach);
    if (!StrongHolds(kCompleted, seq)) {
      return false;
    }
  }
  return true;
}

bool ImplicationHolds(const Word& word, const PropertyExpr& property) {
  if (!property.sequence || !property.lhs) {
    return false;
  }
  const Word kComplement = ComplementWord(word);
  for (std::size_t j = 0; j < word.size(); ++j) {
    if (TightlySatisfies(PrefixInclusive(kComplement, j), *property.sequence) &&
        !Satisfies(Suffix(word, j), *property.lhs)) {
      return false;
    }
  }
  return true;
}

bool UntilLhsHoldsThrough(const Word& word, const PropertyExpr& lhs,
                          std::size_t count) {
  for (std::size_t i = 0; i < count; ++i) {
    if (!Satisfies(Suffix(word, i), lhs)) {
      return false;
    }
  }
  return true;
}

bool UntilReleasedAtSomeIndex(const Word& word, const PropertyExpr& property) {
  for (std::size_t j = 0; j < word.size(); ++j) {
    if (Satisfies(Suffix(word, j), *property.rhs) &&
        UntilLhsHoldsThrough(word, *property.lhs, j)) {
      return true;
    }
  }
  return false;
}

bool UntilHolds(const Word& word, const PropertyExpr& property) {
  if (!property.lhs || !property.rhs) {
    return false;
  }
  return UntilReleasedAtSomeIndex(word, property) ||
         UntilLhsHoldsThrough(word, *property.lhs, word.size());
}

bool AcceptOnHolds(const Word& word, const PropertyExpr& property) {
  if (!property.boolean || !property.lhs) {
    return false;
  }
  if (Satisfies(word, *property.lhs)) {
    return true;
  }
  const std::size_t kReach = PropertyReach(*property.lhs);
  for (std::size_t i = 0; i < word.size(); ++i) {
    if (LetterSatisfiesBoolean(word[i], *property.boolean)) {
      const Word kCompleted =
          PrefixWithTail(FirstLetters(word, i), LetterTop(), kReach);
      if (Satisfies(kCompleted, *property.lhs)) {
        return true;
      }
    }
  }
  return false;
}

bool Satisfies(const Word& word, const PropertyExpr& property) {
  switch (property.kind) {
    case PropertyExpr::Kind::kParen:
      return property.lhs && Satisfies(word, *property.lhs);
    case PropertyExpr::Kind::kNot:
      return property.lhs && !Satisfies(ComplementWord(word), *property.lhs);
    case PropertyExpr::Kind::kStrong:
      return property.sequence && StrongHolds(word, *property.sequence);
    case PropertyExpr::Kind::kWeak:
      return property.sequence && WeakHolds(word, *property.sequence);
    case PropertyExpr::Kind::kImplication:
      return ImplicationHolds(word, property);
    case PropertyExpr::Kind::kOr:
      return (property.lhs && Satisfies(word, *property.lhs)) ||
             (property.rhs && Satisfies(word, *property.rhs));
    case PropertyExpr::Kind::kAnd:
      return property.lhs && property.rhs && Satisfies(word, *property.lhs) &&
             Satisfies(word, *property.rhs);
    case PropertyExpr::Kind::kNexttime:
      return word.empty() ||
             (property.lhs && Satisfies(Suffix(word, 1), *property.lhs));
    case PropertyExpr::Kind::kUntil:
      return UntilHolds(word, property);
    case PropertyExpr::Kind::kAcceptOn:
      return AcceptOnHolds(word, property);
  }
  return false;
}

std::shared_ptr<const PropertyExpr> BridgeClockedProperty(
    const ClockedProperty& q) {
  switch (q.kind) {
    case ClockedProperty::Kind::kBoolean:
      return PropStrong(SeqBoolean(q.boolean));
    case ClockedProperty::Kind::kStrong:
      return PropStrong(q.sequence);
    case ClockedProperty::Kind::kWeak:
      return PropWeak(q.sequence);
    case ClockedProperty::Kind::kNot:
      return PropNot(BridgeClockedProperty(*q.lhs));
    case ClockedProperty::Kind::kImplication:
      return PropImplication(q.sequence, BridgeClockedProperty(*q.lhs));
    case ClockedProperty::Kind::kOr:
      return PropOr(BridgeClockedProperty(*q.lhs),
                    BridgeClockedProperty(*q.rhs));
    case ClockedProperty::Kind::kAnd:
      return PropAnd(BridgeClockedProperty(*q.lhs),
                     BridgeClockedProperty(*q.rhs));
    case ClockedProperty::Kind::kNexttime:
      return PropNexttime(BridgeClockedProperty(*q.lhs));
    case ClockedProperty::Kind::kUntil:
      return PropUntil(BridgeClockedProperty(*q.lhs),
                       BridgeClockedProperty(*q.rhs));
    case ClockedProperty::Kind::kAcceptOn:
      return PropAcceptOn(q.boolean, BridgeClockedProperty(*q.lhs));
    case ClockedProperty::Kind::kClock:
    case ClockedProperty::Kind::kSyncAcceptOn:
    case ClockedProperty::Kind::kDisableIff:
      break;
  }
  return PropStrong(SeqBoolean(BoolTrue()));
}

std::shared_ptr<const PropertyExpr> UnclockProperty(const ClockedProperty& q) {
  return UnclockedPropertyOf(q, BoolTrue());
}

std::shared_ptr<const ClockedProperty> LiftProperty(const PropertyExpr& p) {
  switch (p.kind) {
    case PropertyExpr::Kind::kStrong:
      return ClkStrong(p.sequence);
    case PropertyExpr::Kind::kWeak:
      return ClkWeak(p.sequence);
    case PropertyExpr::Kind::kParen:
      return LiftProperty(*p.lhs);
    case PropertyExpr::Kind::kNot:
      return ClkNot(LiftProperty(*p.lhs));
    case PropertyExpr::Kind::kImplication:
      return ClkImplication(p.sequence, LiftProperty(*p.lhs));
    case PropertyExpr::Kind::kOr:
      return ClkOr(LiftProperty(*p.lhs), LiftProperty(*p.rhs));
    case PropertyExpr::Kind::kAnd:
      return ClkAnd(LiftProperty(*p.lhs), LiftProperty(*p.rhs));
    case PropertyExpr::Kind::kNexttime:
      return ClkNexttime(LiftProperty(*p.lhs));
    case PropertyExpr::Kind::kUntil:
      return ClkUntil(LiftProperty(*p.lhs), LiftProperty(*p.rhs));
    case PropertyExpr::Kind::kAcceptOn:
      return ClkAcceptOn(p.boolean, LiftProperty(*p.lhs));
  }
  return ClkStrong(SeqBoolean(BoolTrue()));
}

std::shared_ptr<const TopLevelProperty> UnclockTopLevel(
    const ClockedTopLevelProperty& u) {
  switch (u.kind) {
    case ClockedTopLevelProperty::Kind::kProperty:
      return TopProperty(UnclockProperty(*u.property));
    case ClockedTopLevelProperty::Kind::kDisableIff:
      return TopDisableIff(u.disable_condition, UnclockProperty(*u.property));
    case ClockedTopLevelProperty::Kind::kParen:
      return TopParen(UnclockTopLevel(*u.inner));
  }
  return TopProperty(PropStrong(SeqBoolean(BoolTrue())));
}

std::shared_ptr<const TopLevelProperty> UnclockTopLevelUnderClock(
    const TopLevelProperty& t,
    const std::shared_ptr<const BooleanExpr>& clock) {
  switch (t.kind) {
    case TopLevelProperty::Kind::kProperty:
      return TopProperty(BridgeClockedProperty(
          *RewritePropertyUnderClock(*LiftProperty(*t.property), clock)));
    case TopLevelProperty::Kind::kDisableIff:
      return TopDisableIff(t.disable_condition,
                           BridgeClockedProperty(*RewritePropertyUnderClock(
                               *LiftProperty(*t.property), clock)));
    case TopLevelProperty::Kind::kParen:
      return TopParen(UnclockTopLevelUnderClock(*t.inner, clock));
  }
  return TopProperty(PropStrong(SeqBoolean(BoolTrue())));
}

std::shared_ptr<const TopLevelProperty> AssertionBody(
    const AssertionStatement& a) {
  if (a.form == AssertionStatement::Form::kExplicitClock) {
    return UnclockTopLevelUnderClock(*a.top, a.clock);
  }
  return UnclockTopLevel(*a.clocked_top);
}

std::shared_ptr<const SequenceExpr> FirstClockTickSequence(
    const std::shared_ptr<const BooleanExpr>& clock) {
  return SeqConcat(SeqZeroOrMoreRepeat(SeqBoolean(BoolNot(clock))),
                   SeqBoolean(clock));
}

}  // namespace

std::shared_ptr<const PropertyExpr> UnclockedPropertyOf(
    const ClockedProperty& q, const std::shared_ptr<const BooleanExpr>& clock) {
  return BridgeClockedProperty(*RewritePropertyUnderClock(q, clock));
}

AssertionActivation ActivationOf(const AssertionStatement& assertion) {
  AssertionActivation activation;
  activation.activation = assertion.activation;
  activation.form = assertion.form;
  activation.clock = assertion.clock;
  return activation;
}

bool ActivationPointEnabled(std::size_t i, const Word& complement,
                            const BooleanExpr& enabling,
                            const AssertionActivation& activation) {
  if (!LetterSatisfiesBoolean(complement[i], enabling)) {
    return false;
  }
  if (activation.activation == AssertionStatement::Activation::kAlways) {
    if (activation.form == AssertionStatement::Form::kExplicitClock) {
      return LetterSatisfiesBoolean(complement[i], *activation.clock);
    }
    return true;
  }
  if (activation.form == AssertionStatement::Form::kExplicitClock) {
    return TightlySatisfies(PrefixInclusive(complement, i),
                            *FirstClockTickSequence(activation.clock));
  }
  return i == 0;
}

namespace {

std::size_t TopLevelReach(const TopLevelProperty& top) {
  if (top.kind == TopLevelProperty::Kind::kParen) {
    return top.inner ? TopLevelReach(*top.inner) : 0;
  }
  return top.property ? PropertyReach(*top.property) : 0;
}

template <typename SuffixFn>
bool HoldsAtActivationPoints(std::size_t count, const Word& complement,
                             const BooleanExpr& enabling,
                             const AssertionStatement& assertion,
                             SuffixFn suffix) {
  const std::shared_ptr<const TopLevelProperty> kBody =
      AssertionBody(assertion);
  const bool kCover = assertion.role == AssertionStatement::Role::kCover;
  for (std::size_t i = 0; i < count; ++i) {
    if (!ActivationPointEnabled(i, complement, enabling,
                                ActivationOf(assertion))) {
      continue;
    }
    const Word kSuffix = suffix(i);
    if (kCover) {
      if (NeutrallySatisfiesTopLevel(kSuffix, *kBody)) {
        return true;
      }
    } else if (FailsTopLevel(kSuffix, *kBody)) {
      return false;
    }
  }
  return !kCover;
}

}  // namespace

bool NeutrallySatisfies(const Word& word, const PropertyExpr& property) {
  return Satisfies(word, property);
}

bool NeutrallySatisfiesTopLevel(const Word& word, const TopLevelProperty& top) {
  switch (top.kind) {
    case TopLevelProperty::Kind::kProperty:
      return top.property && Satisfies(word, *top.property);
    case TopLevelProperty::Kind::kDisableIff: {
      if (!top.disable_condition || !top.property) {
        return false;
      }
      const std::size_t kI = FirstSatisfyingIndex(word, *top.disable_condition);
      if (kI == word.size()) {
        return Satisfies(word, *top.property);
      }
      const std::size_t kReach = PropertyReach(*top.property);
      const Word kCompleted =
          PrefixWithTail(FirstLetters(word, kI), LetterBottom(), kReach);
      return Satisfies(kCompleted, *top.property);
    }
    case TopLevelProperty::Kind::kParen:
      return top.inner && NeutrallySatisfiesTopLevel(word, *top.inner);
  }
  return false;
}

bool DisablesTopLevel(const Word& word, const TopLevelProperty& top) {
  switch (top.kind) {
    case TopLevelProperty::Kind::kProperty:
      return false;
    case TopLevelProperty::Kind::kDisableIff:
      return DisableIffShape(word, top, [](const Word& w, const auto& p) {
        return Satisfies(w, p);
      });
    case TopLevelProperty::Kind::kParen:
      return top.inner && DisablesTopLevel(word, *top.inner);
  }
  return false;
}

bool PassesTopLevel(const Word& word, const TopLevelProperty& top) {
  return NeutrallySatisfiesTopLevel(word, top);
}

bool IsDisabledTopLevel(const Word& word, const TopLevelProperty& top) {
  return DisablesTopLevel(word, top);
}

bool FailsTopLevel(const Word& word, const TopLevelProperty& top) {
  return !PassesTopLevel(word, top) && !IsDisabledTopLevel(word, top);
}

bool NeutrallySatisfiesClockedProperty(const Word& word,
                                       const ClockedProperty& q) {
  return Satisfies(word, *UnclockProperty(q));
}

bool NeutrallySatisfiesTopLevelClocked(const Word& word,
                                       const ClockedTopLevelProperty& top) {
  return NeutrallySatisfiesTopLevel(word, *UnclockTopLevel(top));
}

bool DisablesTopLevelClocked(const Word& word,
                             const ClockedTopLevelProperty& top) {
  return DisablesTopLevel(word, *UnclockTopLevel(top));
}

bool PassesTopLevelClocked(const Word& word,
                           const ClockedTopLevelProperty& top) {
  return NeutrallySatisfiesTopLevelClocked(word, top);
}

bool IsDisabledTopLevelClocked(const Word& word,
                               const ClockedTopLevelProperty& top) {
  return DisablesTopLevelClocked(word, top);
}

bool FailsTopLevelClocked(const Word& word,
                          const ClockedTopLevelProperty& top) {
  return !PassesTopLevelClocked(word, top) &&
         !IsDisabledTopLevelClocked(word, top);
}

bool NeutrallySatisfiesAssertion(const Word& word, const BooleanExpr& enabling,
                                 const AssertionStatement& assertion) {
  return HoldsAtActivationPoints(
      word.size(), ComplementWord(word), enabling, assertion,
      [&word](std::size_t i) { return Suffix(word, i); });
}

bool NeutrallySatisfiesAssertionWithTail(const Word& word, const Letter& tail,
                                         const BooleanExpr& enabling,
                                         const AssertionStatement& assertion) {
  const std::size_t kReach = TopLevelReach(*AssertionBody(assertion));
  Word complement = ComplementWord(word);
  complement.push_back(ComplementLetter(tail));
  return HoldsAtActivationPoints(
      word.size() + 1, complement, enabling, assertion,
      [&word, &tail, kReach](std::size_t i) {
        return PrefixWithTail(Suffix(word, i), tail, kReach);
      });
}

bool WordIsFeasible(const Word& word,
                    const std::vector<EnabledAssertion>& assumptions) {
  for (const EnabledAssertion& assumption : assumptions) {
    if (!NeutrallySatisfiesAssertion(word, *assumption.enabling,
                                     assumption.statement)) {
      return false;
    }
  }
  return true;
}

bool AssertSatisfiedOnWordSet(
    const EnabledAssertion& assertion, const std::vector<Word>& words,
    const std::vector<EnabledAssertion>& assumptions) {
  for (const Word& word : words) {
    if (WordIsFeasible(word, assumptions) &&
        !NeutrallySatisfiesAssertion(word, *assertion.enabling,
                                     assertion.statement)) {
      return false;
    }
  }
  return true;
}

bool CoverSatisfiedOnWordSet(const EnabledAssertion& assertion,
                             const std::vector<Word>& words,
                             const std::vector<EnabledAssertion>& assumptions) {
  for (const Word& word : words) {
    if (WordIsFeasible(word, assumptions) &&
        NeutrallySatisfiesAssertion(word, *assertion.enabling,
                                    assertion.statement)) {
      return true;
    }
  }
  return false;
}

bool HoldsGloballyOnWordSet(const EnabledAssertion& assertion,
                            const std::vector<Word>& words,
                            const std::vector<EnabledAssertion>& assumptions) {
  for (const Word& word : words) {
    if (WordIsFeasible(word, assumptions) &&
        !NeutrallySatisfiesAssertion(word, *assertion.enabling,
                                     assertion.statement)) {
      return false;
    }
  }
  return true;
}

}  // namespace delta
