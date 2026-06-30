#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"

#include <algorithm>
#include <cstddef>
#include <memory>
#include <utility>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"
#include "elaborator/annex_f_word_ops_internal.h"

namespace delta {

std::shared_ptr<const LvProperty> LvStrong(
    std::shared_ptr<const SequenceExpr> r) {
  auto p = std::make_shared<LvProperty>();
  p->kind = LvProperty::Kind::kStrong;
  p->sequence = std::move(r);
  return p;
}

std::shared_ptr<const LvProperty> LvWeak(
    std::shared_ptr<const SequenceExpr> r) {
  auto p = std::make_shared<LvProperty>();
  p->kind = LvProperty::Kind::kWeak;
  p->sequence = std::move(r);
  return p;
}

std::shared_ptr<const LvProperty> LvParen(
    std::shared_ptr<const LvProperty> inner) {
  auto p = std::make_shared<LvProperty>();
  p->kind = LvProperty::Kind::kParen;
  p->lhs = std::move(inner);
  return p;
}

std::shared_ptr<const LvProperty> LvNot(
    std::shared_ptr<const LvProperty> inner) {
  auto p = std::make_shared<LvProperty>();
  p->kind = LvProperty::Kind::kNot;
  p->lhs = std::move(inner);
  return p;
}

std::shared_ptr<const LvProperty> LvImplication(
    std::shared_ptr<const SequenceExpr> antecedent,
    std::shared_ptr<const LvProperty> consequent) {
  auto p = std::make_shared<LvProperty>();
  p->kind = LvProperty::Kind::kImplication;
  p->sequence = std::move(antecedent);
  p->lhs = std::move(consequent);
  return p;
}

std::shared_ptr<const LvProperty> LvOr(std::shared_ptr<const LvProperty> a,
                                       std::shared_ptr<const LvProperty> b) {
  auto p = std::make_shared<LvProperty>();
  p->kind = LvProperty::Kind::kOr;
  p->lhs = std::move(a);
  p->rhs = std::move(b);
  return p;
}

std::shared_ptr<const LvProperty> LvAnd(std::shared_ptr<const LvProperty> a,
                                        std::shared_ptr<const LvProperty> b) {
  auto p = std::make_shared<LvProperty>();
  p->kind = LvProperty::Kind::kAnd;
  p->lhs = std::move(a);
  p->rhs = std::move(b);
  return p;
}

std::shared_ptr<const LvProperty> LvNexttime(
    std::shared_ptr<const LvProperty> inner) {
  auto p = std::make_shared<LvProperty>();
  p->kind = LvProperty::Kind::kNexttime;
  p->lhs = std::move(inner);
  return p;
}

std::shared_ptr<const LvProperty> LvUntil(std::shared_ptr<const LvProperty> a,
                                          std::shared_ptr<const LvProperty> b) {
  auto p = std::make_shared<LvProperty>();
  p->kind = LvProperty::Kind::kUntil;
  p->lhs = std::move(a);
  p->rhs = std::move(b);
  return p;
}

std::shared_ptr<const LvProperty> LvAcceptOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const LvProperty> inner) {
  auto p = std::make_shared<LvProperty>();
  p->kind = LvProperty::Kind::kAcceptOn;
  p->boolean = std::move(b);
  p->lhs = std::move(inner);
  return p;
}

std::shared_ptr<const LvProperty> LvLocalVarDecl(
    std::string type, std::string name,
    std::shared_ptr<const LvProperty> body) {
  auto p = std::make_shared<LvProperty>();
  p->kind = LvProperty::Kind::kLocalVarDecl;
  p->local_var_type = std::move(type);
  p->local_var_name = std::move(name);
  p->lhs = std::move(body);
  return p;
}

std::shared_ptr<const LvTopLevelProperty> LvTopProperty(
    std::shared_ptr<const LvProperty> p) {
  auto t = std::make_shared<LvTopLevelProperty>();
  t->kind = LvTopLevelProperty::Kind::kProperty;
  t->property = std::move(p);
  return t;
}

std::shared_ptr<const LvTopLevelProperty> LvTopDisableIff(
    std::shared_ptr<const BooleanExpr> b, std::shared_ptr<const LvProperty> p) {
  auto t = std::make_shared<LvTopLevelProperty>();
  t->kind = LvTopLevelProperty::Kind::kDisableIff;
  t->disable_condition = std::move(b);
  t->property = std::move(p);
  return t;
}

std::shared_ptr<const LvTopLevelProperty> LvTopParen(
    std::shared_ptr<const LvTopLevelProperty> inner) {
  auto t = std::make_shared<LvTopLevelProperty>();
  t->kind = LvTopLevelProperty::Kind::kParen;
  t->inner = std::move(inner);
  return t;
}

std::shared_ptr<const LvTopLevelProperty> LvTopLocalVarDecl(
    std::string type, std::string name,
    std::shared_ptr<const LvTopLevelProperty> body) {
  auto t = std::make_shared<LvTopLevelProperty>();
  t->kind = LvTopLevelProperty::Kind::kLocalVarDecl;
  t->local_var_type = std::move(type);
  t->local_var_name = std::move(name);
  t->inner = std::move(body);
  return t;
}

namespace {

bool Satisfies(const Word& word, const LvProperty& property,
               const LocalContext& context);

// §F.5.6.1: w, L_0 |= strong(R) iff there exist 0 <= j < |w| and L_1 with
// w^{0,j}, L_0, L_1 |== R. §F.5.5's relation yields the set of such L_1, so the
// existential reduces to that set being nonempty for some prefix.
bool StrongHolds(const Word& word, const SequenceExpr& seq,
                 const LocalContext& context) {
  for (std::size_t j = 0; j < word.size(); ++j) {
    if (!TightSatisfactionOutputs(PrefixInclusive(word, j), seq, context)
             .empty()) {
      return true;
    }
  }
  return false;
}

// §F.5.6.1: w, L_0 |= weak(R) iff for every 0 <= j < |w|, the T^omega-completed
// prefix w^{0,j} T^omega, L_0 |= strong(R).
bool WeakHolds(const Word& word, const SequenceExpr& seq,
               const LocalContext& context) {
  const std::size_t kReach = SequenceReach(seq);
  for (std::size_t j = 0; j < word.size(); ++j) {
    const Word kCompleted =
        PrefixWithTail(PrefixInclusive(word, j), LetterTop(), kReach);
    if (!StrongHolds(kCompleted, seq, context)) {
      return false;
    }
  }
  return true;
}

// §F.5.6.1: w, L_0 |= ( R |-> P ) iff for every 0 <= j < |w| and every output
// context L_1 with w-bar^{0,j}, L_0, L_1 |== R, w^{j.}, L_1 |= P. Each L_1 the
// antecedent yields is threaded into the consequent.
bool ImplicationHolds(const Word& word, const LvProperty& property,
                      const LocalContext& context) {
  if (!property.sequence || !property.lhs) {
    return false;
  }
  const Word kComplement = ComplementWord(word);
  for (std::size_t j = 0; j < word.size(); ++j) {
    for (const LocalContext& out : TightSatisfactionOutputs(
             PrefixInclusive(kComplement, j), *property.sequence, context)) {
      if (!Satisfies(Suffix(word, j), *property.lhs, out)) {
        return false;
      }
    }
  }
  return true;
}

// §F.5.6.1 helper: w^{i.}, L_0 |= P1 holds for every 0 <= i < limit.
bool UntilLhsHoldsThroughLimit(const Word& word, const LvProperty& lhs,
                               const LocalContext& context, std::size_t limit) {
  for (std::size_t i = 0; i < limit; ++i) {
    if (!Satisfies(Suffix(word, i), lhs, context)) {
      return false;
    }
  }
  return true;
}

// §F.5.6.1 helper: some 0 <= j < |w| has w^{j.}, L_0 |= P2 while
// w^{i.}, L_0 |= P1 for all 0 <= i < j.
bool UntilHasReleasingIndex(const Word& word, const LvProperty& property,
                            const LocalContext& context) {
  for (std::size_t j = 0; j < word.size(); ++j) {
    if (Satisfies(Suffix(word, j), *property.rhs, context) &&
        UntilLhsHoldsThroughLimit(word, *property.lhs, context, j)) {
      return true;
    }
  }
  return false;
}

// §F.5.6.1: w, L_0 |= ( P1 until P2 ) iff some 0 <= j < |w| has
// w^{j.}, L_0 |= P2 with w^{i.}, L_0 |= P1 for all 0 <= i < j, or
// w^{i.}, L_0 |= P1 for all i.
bool UntilHolds(const Word& word, const LvProperty& property,
                const LocalContext& context) {
  if (!property.lhs || !property.rhs) {
    return false;
  }
  if (UntilHasReleasingIndex(word, property, context)) {
    return true;
  }
  return UntilLhsHoldsThroughLimit(word, *property.lhs, context, word.size());
}

// §F.5.6.1: w, L_0 |= ( accept_on (b) P ) iff w, L_0 |= P, or for some
// 0 <= i < |w| with w^i |= b, w^{0,i-1} T^omega, L_0 |= P.
bool AcceptOnHolds(const Word& word, const LvProperty& property,
                   const LocalContext& context) {
  if (!property.boolean || !property.lhs) {
    return false;
  }
  if (Satisfies(word, *property.lhs, context)) {
    return true;
  }
  const std::size_t kReach = PropertyReach(*property.lhs);
  for (std::size_t i = 0; i < word.size(); ++i) {
    if (LetterSatisfiesBoolean(word[i], *property.boolean)) {
      const Word kCompleted =
          PrefixWithTail(FirstLetters(word, i), LetterTop(), kReach);
      if (Satisfies(kCompleted, *property.lhs, context)) {
        return true;
      }
    }
  }
  return false;
}

bool Satisfies(const Word& word, const LvProperty& property,
               const LocalContext& context) {
  switch (property.kind) {
    case LvProperty::Kind::kLocalVarDecl:
      // §F.5.6.1: w, L_0 |= ( t v ; P ) iff w, L_0\v |= P. The declared name is
      // stripped from the context the body sees.
      return property.lhs &&
             Satisfies(word, *property.lhs,
                       RemoveName(context, property.local_var_name));
    case LvProperty::Kind::kParen:
      // §F.5.6.1: w, L_0 |= ( P ) iff w, L_0 |= P.
      return property.lhs && Satisfies(word, *property.lhs, context);
    case LvProperty::Kind::kNot:
      // §F.5.6.1: w, L_0 |= not P iff w-bar, L_0 |= P. Negation is by word
      // complementation, matching the plain neutral-satisfaction rule (the
      // result is not logically negated).
      return property.lhs &&
             Satisfies(ComplementWord(word), *property.lhs, context);
    case LvProperty::Kind::kStrong:
      // §F.5.6.1: strong(R) over the four-way tight-satisfaction relation.
      return property.sequence &&
             StrongHolds(word, *property.sequence, context);
    case LvProperty::Kind::kWeak:
      // §F.5.6.1: weak(R) over the four-way tight-satisfaction relation.
      return property.sequence && WeakHolds(word, *property.sequence, context);
    case LvProperty::Kind::kImplication:
      return ImplicationHolds(word, property, context);
    case LvProperty::Kind::kOr:
      // §F.5.6.1: w, L_0 |= ( P1 or P2 ) iff w, L_0 |= P1 or w, L_0 |= P2.
      return (property.lhs && Satisfies(word, *property.lhs, context)) ||
             (property.rhs && Satisfies(word, *property.rhs, context));
    case LvProperty::Kind::kAnd:
      // §F.5.6.1: w, L_0 |= ( P1 and P2 ) iff w, L_0 |= P1 and w, L_0 |= P2.
      return property.lhs && property.rhs &&
             Satisfies(word, *property.lhs, context) &&
             Satisfies(word, *property.rhs, context);
    case LvProperty::Kind::kNexttime:
      // §F.5.6.1: w, L_0 |= ( nexttime P ) iff |w| = 0 or w^{1.}, L_0 |= P.
      return word.empty() ||
             (property.lhs &&
              Satisfies(Suffix(word, 1), *property.lhs, context));
    case LvProperty::Kind::kUntil:
      return UntilHolds(word, property, context);
    case LvProperty::Kind::kAcceptOn:
      return AcceptOnHolds(word, property, context);
  }
  return false;
}

}  // namespace

bool NeutrallySatisfiesWithLocals(const Word& word, const LvProperty& property,
                                  const LocalContext& context) {
  return Satisfies(word, property, context);
}

bool NeutrallySatisfiesWithLocals(const Word& word,
                                  const LvProperty& property) {
  // §F.5.6.1: "w |= Q iff w, {} |= Q" -- start from the empty context.
  return Satisfies(word, property, LocalContext{});
}

bool NeutrallySatisfiesTopLevelWithLocals(const Word& word,
                                          const LvTopLevelProperty& top,
                                          const LocalContext& context) {
  switch (top.kind) {
    case LvTopLevelProperty::Kind::kProperty:
      // §F.5.6.1: for T = P, w, L_0 |= T iff w, L_0 |= P.
      return top.property && Satisfies(word, *top.property, context);
    case LvTopLevelProperty::Kind::kDisableIff: {
      // §F.5.6.1: for T = disable iff (b) P, w, L_0 |= T iff either w, L_0 |= P
      // and no letter of w satisfies b, or some letter satisfies b and
      // w^{0,i-1} _|_^omega, L_0 |= P for i the least index with w^i |= b.
      if (!top.disable_condition || !top.property) {
        return false;
      }
      const std::size_t kI = FirstSatisfyingIndex(word, *top.disable_condition);
      if (kI == word.size()) {
        return Satisfies(word, *top.property, context);
      }
      const std::size_t kReach = PropertyReach(*top.property);
      const Word kCompleted =
          PrefixWithTail(FirstLetters(word, kI), LetterBottom(), kReach);
      return Satisfies(kCompleted, *top.property, context);
    }
    case LvTopLevelProperty::Kind::kParen:
      // §F.5.6.1: w, L_0 |= ( T ) iff w, L_0 |= T.
      return top.inner &&
             NeutrallySatisfiesTopLevelWithLocals(word, *top.inner, context);
    case LvTopLevelProperty::Kind::kLocalVarDecl:
      // §F.5.6.1: w, L_0 |= ( t v ; T ) iff w, L_0\v |= T.
      return top.inner &&
             NeutrallySatisfiesTopLevelWithLocals(
                 word, *top.inner, RemoveName(context, top.local_var_name));
  }
  return false;
}

bool DisablesTopLevelWithLocals(const Word& word, const LvTopLevelProperty& top,
                                const LocalContext& context) {
  switch (top.kind) {
    case LvTopLevelProperty::Kind::kProperty:
      // §F.5.6.1: for T = P, w, L_0 |=^d T never holds.
      return false;
    case LvTopLevelProperty::Kind::kDisableIff:
      // §F.5.6.1: for T = disable iff (b) P, w, L_0 |=^d T iff some letter of w
      // satisfies b and both w^{0,i-1} T^omega, L_0 |= P and
      // w^{0,i-1} _|_^omega, L_0 |/= P for i the least index with w^i |= b.
      return DisableIffShape(word, top,
                             [&context](const Word& w, const auto& p) {
                               return Satisfies(w, p, context);
                             });
    case LvTopLevelProperty::Kind::kParen:
      // §F.5.6.1: w, L_0 |=^d ( T ) iff w, L_0 |=^d T.
      return top.inner && DisablesTopLevelWithLocals(word, *top.inner, context);
    case LvTopLevelProperty::Kind::kLocalVarDecl:
      // §F.5.6.1: w, L_0 |=^d ( t v ; T ) iff w, L_0\v |=^d T.
      return top.inner &&
             DisablesTopLevelWithLocals(
                 word, *top.inner, RemoveName(context, top.local_var_name));
  }
  return false;
}

bool PassesTopLevelWithLocals(const Word& word, const LvTopLevelProperty& top,
                              const LocalContext& context) {
  // §F.5.6.1: "T is said to pass on w, L_0 if w, L_0 |= T."
  return NeutrallySatisfiesTopLevelWithLocals(word, top, context);
}

bool IsDisabledTopLevelWithLocals(const Word& word,
                                  const LvTopLevelProperty& top,
                                  const LocalContext& context) {
  // §F.5.6.1: "T is said to be disabled on w, L_0 if w, L_0 |=^d T."
  return DisablesTopLevelWithLocals(word, top, context);
}

bool FailsTopLevelWithLocals(const Word& word, const LvTopLevelProperty& top,
                             const LocalContext& context) {
  // §F.5.6.1: "T is said to fail on w, L_0 if T neither passes nor is disabled
  // on w, L_0." Pass and disabled are mutually exclusive, so failure is their
  // joint negation.
  return !PassesTopLevelWithLocals(word, top, context) &&
         !IsDisabledTopLevelWithLocals(word, top, context);
}

}  // namespace delta
