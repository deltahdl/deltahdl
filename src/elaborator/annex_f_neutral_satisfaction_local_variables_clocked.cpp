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
  const std::shared_ptr<const LvTopLevelProperty> kBody =
      UnclockTopLevelWithLocals(*assertion.body, BodyClock(assertion));
  AssertionActivation activation;
  activation.activation = assertion.activation;
  activation.form = assertion.form;
  activation.clock = assertion.clock;
  const Word kComplement = ComplementWord(word);
  const bool kCover = assertion.role == AssertionStatement::Role::kCover;
  for (std::size_t i = 0; i < word.size(); ++i) {
    if (!ActivationPointEnabled(i, kComplement, enabling, activation)) {
      continue;
    }
    const Word kSuffix = Suffix(word, i);
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

}  // namespace delta
