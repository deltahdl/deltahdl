#include "elaborator/annex_f_neutral_satisfaction_local_variables_clocked.h"

#include <cstddef>
#include <memory>
#include <string>
#include <utility>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_satisfaction_without_local_variables.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"
#include "elaborator/annex_f_word_ops_internal.h"

namespace delta {
namespace {

// §F.5.6.1: T^p(Q, c) read into the property model and embedded with local
// variables, the property the unclocked layer decides.
std::shared_ptr<const LvProperty> UnclockWithLocals(
    const ClockedProperty& q, const std::shared_ptr<const BooleanExpr>& clock) {
  return AsPropertyWithLocalVariables(*UnclockedPropertyOf(q, clock));
}

std::shared_ptr<LvClockedTopLevelProperty> MakeTop(
    LvClockedTopLevelProperty::Kind kind) {
  auto top = std::make_shared<LvClockedTopLevelProperty>();
  top->kind = kind;
  return top;
}

// The clock the body of an assertion statement is decided under: c for
// @( c ) T, and 1 for U.
std::shared_ptr<const BooleanExpr> BodyClock(const LvAssertionStatement& a) {
  if (a.form == AssertionStatement::Form::kExplicitClock) {
    return a.clock;
  }
  return BoolTrue();
}

// The unclocked top-level property with local variables an assertion
// statement evaluates at each activation point.
std::shared_ptr<const LvTopLevelProperty> LvAssertionBody(
    const LvAssertionStatement& a) {
  return UnclockTopLevelWithLocals(*a.body, BodyClock(a));
}

// The activation, form and clock of a statement, by which §F.5.3.1's
// activation rule decides its activation points.
AssertionActivation ActivationOfWithLocals(const LvAssertionStatement& a) {
  AssertionActivation activation;
  activation.activation = a.activation;
  activation.form = a.form;
  activation.clock = a.clock;
  return activation;
}

// The reach of the body: that of the property under its guard, parenthesis
// and declaration.
std::size_t LvTopLevelReach(const LvTopLevelProperty& top) {
  if (top.kind == LvTopLevelProperty::Kind::kParen ||
      top.kind == LvTopLevelProperty::Kind::kLocalVarDecl) {
    return top.inner ? LvTopLevelReach(*top.inner) : 0;
  }
  return top.property ? PropertyReach(*top.property) : 0;
}

// §F.5.6.1: the scan over activation points both assertion relations share,
// as §F.5.3.1's: the points 0 .. count-1 are tried against `complement`, and
// the body is decided from the empty context on the suffix `suffix` gives for
// each enabled one; an assert or assume statement requires that it not fail
// at every enabled point, a cover statement that it pass at some.
template <typename SuffixFn>
bool HoldsAtActivationPointsWithLocals(std::size_t count,
                                       const Word& complement,
                                       const BooleanExpr& enabling,
                                       const LvAssertionStatement& assertion,
                                       SuffixFn suffix) {
  const std::shared_ptr<const LvTopLevelProperty> kBody =
      LvAssertionBody(assertion);
  const AssertionActivation kActivation = ActivationOfWithLocals(assertion);
  const bool kCover = assertion.role == AssertionStatement::Role::kCover;
  for (std::size_t i = 0; i < count; ++i) {
    if (!ActivationPointEnabled(i, complement, enabling, kActivation)) {
      continue;
    }
    const Word kSuffix = suffix(i);
    if (kCover) {
      if (PassesTopLevelWithLocals(kSuffix, *kBody, LocalContext{})) {
        return true;
      }
    } else if (FailsTopLevelWithLocals(kSuffix, *kBody, LocalContext{})) {
      return false;
    }
  }
  return !kCover;
}

}  // namespace

bool NeutrallySatisfiesClockedPropertyWithLocals(const Word& word,
                                                 const ClockedProperty& q,
                                                 const LocalContext& context) {
  // §F.5.6.1: w, L_0 |= Q iff w, L_0 |= T^p(Q, 1).
  return NeutrallySatisfiesWithLocals(word, *UnclockWithLocals(q, BoolTrue()),
                                      context);
}

std::shared_ptr<const LvClockedTopLevelProperty> LvClockedTopProperty(
    std::shared_ptr<const ClockedProperty> q) {
  auto top = MakeTop(LvClockedTopLevelProperty::Kind::kProperty);
  top->property = std::move(q);
  return top;
}

std::shared_ptr<const LvClockedTopLevelProperty> LvClockedTopDisableIff(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> q) {
  auto top = MakeTop(LvClockedTopLevelProperty::Kind::kDisableIff);
  top->disable_condition = std::move(b);
  top->property = std::move(q);
  return top;
}

std::shared_ptr<const LvClockedTopLevelProperty> LvClockedTopParen(
    std::shared_ptr<const LvClockedTopLevelProperty> inner) {
  auto top = MakeTop(LvClockedTopLevelProperty::Kind::kParen);
  top->inner = std::move(inner);
  return top;
}

std::shared_ptr<const LvClockedTopLevelProperty> LvClockedTopLocalVarDecl(
    std::string type, std::string name,
    std::shared_ptr<const LvClockedTopLevelProperty> body) {
  auto top = MakeTop(LvClockedTopLevelProperty::Kind::kLocalVarDecl);
  top->local_var_type = std::move(type);
  top->local_var_name = std::move(name);
  top->inner = std::move(body);
  return top;
}

std::shared_ptr<const LvTopLevelProperty> UnclockTopLevelWithLocals(
    const LvClockedTopLevelProperty& top,
    const std::shared_ptr<const BooleanExpr>& clock) {
  switch (top.kind) {
    case LvClockedTopLevelProperty::Kind::kProperty:
      // §F.5.6.1: for U = Q, w, L_0 |= U iff w, L_0 |= Q.
      return LvTopProperty(UnclockWithLocals(*top.property, clock));
    case LvClockedTopLevelProperty::Kind::kDisableIff:
      // §F.5.6.1: the disable iff rule for U is the T rule with Q for P.
      return LvTopDisableIff(top.disable_condition,
                             UnclockWithLocals(*top.property, clock));
    case LvClockedTopLevelProperty::Kind::kParen:
      // §F.5.6.1: w, L_0 |= ( U ) iff w, L_0 |= U.
      return LvTopParen(UnclockTopLevelWithLocals(*top.inner, clock));
    case LvClockedTopLevelProperty::Kind::kLocalVarDecl:
      // §F.5.6.1: w, L_0 |= ( t v ; U ) iff w, L_0\v |= U, which the T form
      // of the same shape decides.
      return LvTopLocalVarDecl(top.local_var_type, top.local_var_name,
                               UnclockTopLevelWithLocals(*top.inner, clock));
  }
  return LvTopProperty(LvStrong(SeqBoolean(BoolTrue())));
}

bool NeutrallySatisfiesTopLevelClockedWithLocals(
    const Word& word, const LvClockedTopLevelProperty& top,
    const LocalContext& context) {
  return NeutrallySatisfiesTopLevelWithLocals(
      word, *UnclockTopLevelWithLocals(top, BoolTrue()), context);
}

bool DisablesTopLevelClockedWithLocals(const Word& word,
                                       const LvClockedTopLevelProperty& top,
                                       const LocalContext& context) {
  return DisablesTopLevelWithLocals(
      word, *UnclockTopLevelWithLocals(top, BoolTrue()), context);
}

bool PassesTopLevelClockedWithLocals(const Word& word,
                                     const LvClockedTopLevelProperty& top,
                                     const LocalContext& context) {
  // §F.5.6.1: "T is said to pass on w, L_0 if w, L_0 |= T", U alike.
  return NeutrallySatisfiesTopLevelClockedWithLocals(word, top, context);
}

bool IsDisabledTopLevelClockedWithLocals(const Word& word,
                                         const LvClockedTopLevelProperty& top,
                                         const LocalContext& context) {
  // §F.5.6.1: "T is said to be disabled on w, L_0 if w, L_0 |=^d T".
  return DisablesTopLevelClockedWithLocals(word, top, context);
}

bool FailsTopLevelClockedWithLocals(const Word& word,
                                    const LvClockedTopLevelProperty& top,
                                    const LocalContext& context) {
  // §F.5.6.1: "T is said to fail on w, L_0 if T neither passes nor is
  // disabled on w, L_0."
  return !PassesTopLevelClockedWithLocals(word, top, context) &&
         !IsDisabledTopLevelClockedWithLocals(word, top, context);
}

std::shared_ptr<const LvAssertionStatement> LvAssertionWithClock(
    AssertionStatement::Activation activation, AssertionStatement::Role role,
    std::shared_ptr<const BooleanExpr> clock,
    std::shared_ptr<const LvClockedTopLevelProperty> top) {
  auto a = std::make_shared<LvAssertionStatement>();
  a->activation = activation;
  a->role = role;
  a->form = AssertionStatement::Form::kExplicitClock;
  a->clock = std::move(clock);
  a->body = std::move(top);
  return a;
}

std::shared_ptr<const LvAssertionStatement> LvAssertionWithClockedTop(
    AssertionStatement::Activation activation, AssertionStatement::Role role,
    std::shared_ptr<const LvClockedTopLevelProperty> clocked_top) {
  auto a = std::make_shared<LvAssertionStatement>();
  a->activation = activation;
  a->role = role;
  a->form = AssertionStatement::Form::kClockedTop;
  a->body = std::move(clocked_top);
  return a;
}

bool NeutrallySatisfiesAssertionWithLocals(
    const Word& word, const BooleanExpr& enabling,
    const LvAssertionStatement& assertion) {
  // §F.5.6.1: the rules of §F.5.3.1, the body decided from the empty context
  // at each enabled activation point.
  return HoldsAtActivationPointsWithLocals(
      word.size(), ComplementWord(word), enabling, assertion,
      [&word](std::size_t i) { return Suffix(word, i); });
}

bool NeutrallySatisfiesAssertionWithLocalsWithTail(
    const Word& word, const Letter& tail, const BooleanExpr& enabling,
    const LvAssertionStatement& assertion) {
  // The complement of w tail^omega is w-bar followed by the complement of the
  // tail forever; the point at index |w| stands for every point in the tail,
  // as in §F.5.3.1's NeutrallySatisfiesAssertionWithTail.
  const std::size_t kReach = LvTopLevelReach(*LvAssertionBody(assertion));
  Word complement = ComplementWord(word);
  complement.push_back(ComplementLetter(tail));
  return HoldsAtActivationPointsWithLocals(
      word.size() + 1, complement, enabling, assertion,
      [&word, &tail, kReach](std::size_t i) {
        return PrefixWithTail(Suffix(word, i), tail, kReach);
      });
}

}  // namespace delta
