#include "elaborator/annex_f_neutral_satisfaction.h"

#include <algorithm>
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

// §F.5.3.1: w |= strong(R) iff there exists 0 <= j < |w| with w^{0,j} |= R.
bool StrongHolds(const Word& word, const SequenceExpr& seq) {
  for (std::size_t j = 0; j < word.size(); ++j) {
    if (TightlySatisfies(PrefixInclusive(word, j), seq)) {
      return true;
    }
  }
  return false;
}

bool Satisfies(const Word& word, const PropertyExpr& property);

// §F.5.3.1: w |= weak(R) iff for every 0 <= j < |w|, w^{0,j} T^omega |=
// strong(R).
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

// §F.5.3.1: w |= ( R |-> P ) iff for every 0 <= j < |w| with w-bar^{0,j} |= R,
// w^{j.} |= P.
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

// §F.5.3.1: w |= ( P1 until P2 ) iff some 0 <= j < |w| has w^{j.} |= P2 with
// w^{i.} |= P1 for all 0 <= i < j, or w^{i.} |= P1 for all i.
bool UntilHolds(const Word& word, const PropertyExpr& property) {
  if (!property.lhs || !property.rhs) {
    return false;
  }
  for (std::size_t j = 0; j < word.size(); ++j) {
    if (Satisfies(Suffix(word, j), *property.rhs)) {
      bool prefix_holds = true;
      for (std::size_t i = 0; i < j; ++i) {
        if (!Satisfies(Suffix(word, i), *property.lhs)) {
          prefix_holds = false;
          break;
        }
      }
      if (prefix_holds) {
        return true;
      }
    }
  }
  for (std::size_t i = 0; i < word.size(); ++i) {
    if (!Satisfies(Suffix(word, i), *property.lhs)) {
      return false;
    }
  }
  return true;
}

// §F.5.3.1: w |= ( accept_on (b) P ) iff w |= P, or for some 0 <= i < |w| with
// w^i |= b, w^{0,i-1} T^omega |= P.
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
      // §F.5.3.1: w |= ( P ) iff w |= P.
      return property.lhs && Satisfies(word, *property.lhs);
    case PropertyExpr::Kind::kNot:
      // §F.5.3.1: w |= not P iff w-bar |= P.
      return property.lhs && Satisfies(ComplementWord(word), *property.lhs);
    case PropertyExpr::Kind::kStrong:
      // §F.5.3.1: w |= strong(R) iff some w^{0,j} tightly satisfies R.
      return property.sequence && StrongHolds(word, *property.sequence);
    case PropertyExpr::Kind::kWeak:
      // §F.5.3.1: w |= weak(R) iff every T^omega-completed prefix satisfies
      // strong(R).
      return property.sequence && WeakHolds(word, *property.sequence);
    case PropertyExpr::Kind::kImplication:
      return ImplicationHolds(word, property);
    case PropertyExpr::Kind::kOr:
      // §F.5.3.1: w |= ( P1 or P2 ) iff w |= P1 or w |= P2.
      return (property.lhs && Satisfies(word, *property.lhs)) ||
             (property.rhs && Satisfies(word, *property.rhs));
    case PropertyExpr::Kind::kAnd:
      // §F.5.3.1: w |= ( P1 and P2 ) iff w |= P1 and w |= P2.
      return property.lhs && property.rhs && Satisfies(word, *property.lhs) &&
             Satisfies(word, *property.rhs);
    case PropertyExpr::Kind::kNexttime:
      // §F.5.3.1: w |= ( nexttime P ) iff |w| = 0 or w^{1.} |= P.
      return word.empty() ||
             (property.lhs && Satisfies(Suffix(word, 1), *property.lhs));
    case PropertyExpr::Kind::kUntil:
      return UntilHolds(word, property);
    case PropertyExpr::Kind::kAcceptOn:
      return AcceptOnHolds(word, property);
  }
  return false;
}

// Maps a §F.5.1.2 ClockedProperty that no longer contains a clock or
// sync_accept_on form -- i.e. the output of T^p -- onto the §F.5.3.1
// PropertyExpr the unclocked evaluator understands. A bare Boolean in property
// position (emitted by the nexttime and until rules of T^p for the clock c) is
// read as strong(b): a Boolean is a length-one sequence, and strong(b) and
// weak(b) coincide on it, both holding exactly when the first letter models b.
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
      // T^p eliminates the clock and sync_accept_on forms, and disable iff is a
      // top-level form that never appears inside a property Q, so these are not
      // reachable from a T^p result. Fall through to a benign leaf.
      break;
  }
  return PropStrong(SeqBoolean(BoolTrue()));
}

// §F.5.3.1: the unclocked property that decides w |= Q, namely T^p(Q, 1)
// bridged into a PropertyExpr. §F.5.1.2's RewritePropertyUnderClock is the
// satisfied dependency that supplies T^p.
std::shared_ptr<const PropertyExpr> UnclockProperty(const ClockedProperty& q) {
  return BridgeClockedProperty(*RewritePropertyUnderClock(q, BoolTrue()));
}

// Lifts an unclocked property P into the §F.5.1.2 ClockedProperty model so an
// explicit clock @( c ) can be pushed onto it by T^p. The forms correspond
// one-to-one; a parenthesis is transparent, matching w |= ( P ) iff w |= P.
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

// Reduces a clocked top-level property U to the unclocked top-level property
// that decides it: each form mirrors its T counterpart with the unclocked
// property T^p(Q, 1) in place of P.
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

// Reduces @( c ) T to the unclocked top-level property that decides it. The
// clock c is pushed onto the guarded property via T^p(., c); the disable iff
// guard and parentheses carry through unchanged.
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

// The unclocked top-level property an assertion statement evaluates at each
// activation point: @( c ) T resolved under its clock, or U reduced.
std::shared_ptr<const TopLevelProperty> AssertionBody(
    const AssertionStatement& a) {
  if (a.form == AssertionStatement::Form::kExplicitClock) {
    return UnclockTopLevelUnderClock(*a.top, a.clock);
  }
  return UnclockTopLevel(*a.clocked_top);
}

// §F.5.3.1: the activation sequence !c [*0:$] ##1 c. The initial forms fire at
// the first index whose prefix tightly satisfies it, i.e. the first clock tick.
std::shared_ptr<const SequenceExpr> FirstClockTickSequence(
    const std::shared_ptr<const BooleanExpr>& clock) {
  return SeqConcat(SeqZeroOrMoreRepeat(SeqBoolean(BoolNot(clock))),
                   SeqBoolean(clock));
}

// §F.5.3.1: every rule guards an activation point i by the enabling condition
// (w-bar^i |= b) and, depending on activation and form, by the clock. The
// always forms scan every index; the initial forms fire only at the first
// clock tick (clocked) or at index 0 (the U column). kComplement is w-bar.
bool ActivationPointEnabled(std::size_t i, const Word& complement,
                            const BooleanExpr& enabling,
                            const AssertionStatement& assertion) {
  if (!LetterSatisfiesBoolean(complement[i], enabling)) {
    return false;
  }
  if (assertion.activation == AssertionStatement::Activation::kAlways) {
    if (assertion.form == AssertionStatement::Form::kExplicitClock) {
      return LetterSatisfiesBoolean(complement[i], *assertion.clock);
    }
    return true;
  }
  if (assertion.form == AssertionStatement::Form::kExplicitClock) {
    return TightlySatisfies(PrefixInclusive(complement, i),
                            *FirstClockTickSequence(assertion.clock));
  }
  return i == 0;
}

}  // namespace

bool NeutrallySatisfies(const Word& word, const PropertyExpr& property) {
  return Satisfies(word, property);
}

bool NeutrallySatisfiesTopLevel(const Word& word, const TopLevelProperty& top) {
  switch (top.kind) {
    case TopLevelProperty::Kind::kProperty:
      // §F.5.3.1: for T = P, w |= T iff w |= P.
      return top.property && Satisfies(word, *top.property);
    case TopLevelProperty::Kind::kDisableIff: {
      // §F.5.3.1: for T = disable iff (b) P, w |= T iff either w |= P and no
      // letter of w satisfies b, or some letter satisfies b and
      // w^{0,i-1} _|_^omega |= P for i the least index with w^i |= b.
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
      // §F.5.3.1: w |= ( T ) iff w |= T.
      return top.inner && NeutrallySatisfiesTopLevel(word, *top.inner);
  }
  return false;
}

bool DisablesTopLevel(const Word& word, const TopLevelProperty& top) {
  switch (top.kind) {
    case TopLevelProperty::Kind::kProperty:
      // §F.5.3.1: for T = P, w |=^d T never holds.
      return false;
    case TopLevelProperty::Kind::kDisableIff:
      // §F.5.3.1: for T = disable iff (b) P, w |=^d T iff some letter of w
      // satisfies b and both w^{0,i-1} T^omega |= P and w^{0,i-1} _|_^omega
      // |/= P for i the least index with w^i |= b.
      return DisableIffShape(word, top, [](const Word& w, const auto& p) {
        return Satisfies(w, p);
      });
    case TopLevelProperty::Kind::kParen:
      // §F.5.3.1: w |=^d ( T ) iff w |=^d T.
      return top.inner && DisablesTopLevel(word, *top.inner);
  }
  return false;
}

bool PassesTopLevel(const Word& word, const TopLevelProperty& top) {
  // §F.5.3.1: "T is said to pass on w if w |= T."
  return NeutrallySatisfiesTopLevel(word, top);
}

bool IsDisabledTopLevel(const Word& word, const TopLevelProperty& top) {
  // §F.5.3.1: "T is said to be disabled on w if w |=^d T."
  return DisablesTopLevel(word, top);
}

bool FailsTopLevel(const Word& word, const TopLevelProperty& top) {
  // §F.5.3.1: "T is said to fail on w if T neither passes nor is disabled on
  // w." Pass and disabled are mutually exclusive, so failure is their joint
  // negation.
  return !PassesTopLevel(word, top) && !IsDisabledTopLevel(word, top);
}

bool NeutrallySatisfiesClockedProperty(const Word& word,
                                       const ClockedProperty& q) {
  // §F.5.3.1: w |= Q iff w |= T^p(Q, 1).
  return Satisfies(word, *UnclockProperty(q));
}

bool NeutrallySatisfiesTopLevelClocked(const Word& word,
                                       const ClockedTopLevelProperty& top) {
  // §F.5.3.1: the U rules mirror the T rules with Q for P. Reduce U to the
  // deciding unclocked top-level property and apply the T satisfaction.
  return NeutrallySatisfiesTopLevel(word, *UnclockTopLevel(top));
}

bool DisablesTopLevelClocked(const Word& word,
                             const ClockedTopLevelProperty& top) {
  // §F.5.3.1: likewise for w |=^d U.
  return DisablesTopLevel(word, *UnclockTopLevel(top));
}

bool PassesTopLevelClocked(const Word& word,
                           const ClockedTopLevelProperty& top) {
  // §F.5.3.1: "pass on w if w |= U".
  return NeutrallySatisfiesTopLevelClocked(word, top);
}

bool IsDisabledTopLevelClocked(const Word& word,
                               const ClockedTopLevelProperty& top) {
  // §F.5.3.1: "disabled on w if w |=^d U".
  return DisablesTopLevelClocked(word, top);
}

bool FailsTopLevelClocked(const Word& word,
                          const ClockedTopLevelProperty& top) {
  // §F.5.3.1: "fail on w if U neither passes nor is disabled on w".
  return !PassesTopLevelClocked(word, top) &&
         !IsDisabledTopLevelClocked(word, top);
}

bool NeutrallySatisfiesAssertion(const Word& word, const BooleanExpr& enabling,
                                 const AssertionStatement& assertion) {
  const std::shared_ptr<const TopLevelProperty> kBody =
      AssertionBody(assertion);
  const Word kComplement = ComplementWord(word);
  const bool kCover = assertion.role == AssertionStatement::Role::kCover;

  for (std::size_t i = 0; i < word.size(); ++i) {
    if (!ActivationPointEnabled(i, kComplement, enabling, assertion)) {
      continue;
    }
    const Word kSuffix = Suffix(word, i);
    if (kCover) {
      // §F.5.3.1: a cover statement holds when the body passes at some enabled
      // activation point.
      if (NeutrallySatisfiesTopLevel(kSuffix, *kBody)) {
        return true;
      }
    } else if (FailsTopLevel(kSuffix, *kBody)) {
      // §F.5.3.1: an assert or assume statement requires that the body pass or
      // be disabled (i.e. not fail) at every enabled activation point. assume
      // statements share the assert definition.
      return false;
    }
  }
  // No enabled activation falsified an assert/assume statement, so it holds; a
  // cover statement with no satisfying activation does not.
  return !kCover;
}

bool WordIsFeasible(const Word& word,
                    const std::vector<EnabledAssertion>& assumptions) {
  // §F.5.3.1: a word is feasible iff every assumption is satisfied on it.
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
  // §F.5.3.1: an assert statement is satisfied on the set iff it is satisfied
  // on each feasible word.
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
  // §F.5.3.1: a cover statement is satisfied on the set iff it is satisfied on
  // at least one feasible word.
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
  // §F.5.3.1: an assertion statement holds globally on the set iff it is
  // satisfied on every feasible word.
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
