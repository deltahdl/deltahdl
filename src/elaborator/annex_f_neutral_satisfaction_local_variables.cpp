#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"

#include <algorithm>
#include <cstddef>
#include <memory>
#include <utility>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

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

// §F.5: the first i letters w^{0,i-1}; the empty word when i = 0.
Word FirstLetters(const Word& word, std::size_t i) {
  const std::size_t count = std::min(i, word.size());
  return Word(word.begin(), word.begin() + static_cast<std::ptrdiff_t>(count));
}

// A structural bound on how far a sequence can reach into a word, mirroring
// §F.5.3.1: unbounded repeats are bounded by a single iteration, the shortest
// witness on a constant T^omega tail.
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

// A structural bound on how far a property can reach into a word, used to size
// the constant T^omega / _|_^omega tails for the disable iff and accept_on
// completions, mirroring §F.5.3.1.
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

// A finite materialization of w^{0,i-1} followed by a constant tail (T^omega or
// _|_^omega), padded past `reach` so the verdict has stabilized, mirroring
// §F.5.3.1's bounded witness search.
Word PrefixWithTail(const Word& prefix, const Letter& tail, std::size_t reach) {
  Word out = prefix;
  const std::size_t pad = reach + 2;
  for (std::size_t i = 0; i < pad; ++i) {
    out.push_back(tail);
  }
  return out;
}

// The least index at which a letter of the word satisfies b, or word.size() if
// none does.
std::size_t FirstSatisfyingIndex(const Word& word, const BooleanExpr& b) {
  for (std::size_t i = 0; i < word.size(); ++i) {
    if (LetterSatisfiesBoolean(word[i], b)) {
      return i;
    }
  }
  return word.size();
}

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
  const std::size_t reach = SequenceReach(seq);
  for (std::size_t j = 0; j < word.size(); ++j) {
    const Word completed =
        PrefixWithTail(PrefixInclusive(word, j), LetterTop(), reach);
    if (!StrongHolds(completed, seq, context)) {
      return false;
    }
  }
  return true;
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
      // §F.5.6.1: w, L_0 |= not P iff w-bar, L_0 |/= P.
      return property.lhs &&
             !Satisfies(ComplementWord(word), *property.lhs, context);
    case LvProperty::Kind::kStrong:
      // §F.5.6.1: strong(R) over the four-way tight-satisfaction relation.
      return property.sequence &&
             StrongHolds(word, *property.sequence, context);
    case LvProperty::Kind::kWeak:
      // §F.5.6.1: weak(R) over the four-way tight-satisfaction relation.
      return property.sequence && WeakHolds(word, *property.sequence, context);
    case LvProperty::Kind::kImplication: {
      // §F.5.6.1: w, L_0 |= ( R |-> P ) iff for every 0 <= j < |w| and every
      // output context L_1 with w-bar^{0,j}, L_0, L_1 |== R, w^{j.}, L_1 |= P.
      // Each L_1 the antecedent yields is threaded into the consequent.
      if (!property.sequence || !property.lhs) {
        return false;
      }
      const Word complement = ComplementWord(word);
      for (std::size_t j = 0; j < word.size(); ++j) {
        for (const LocalContext& out : TightSatisfactionOutputs(
                 PrefixInclusive(complement, j), *property.sequence, context)) {
          if (!Satisfies(Suffix(word, j), *property.lhs, out)) {
            return false;
          }
        }
      }
      return true;
    }
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
    case LvProperty::Kind::kUntil: {
      // §F.5.6.1: w, L_0 |= ( P1 until P2 ) iff some 0 <= j < |w| has
      // w^{j.}, L_0 |= P2 with w^{i.}, L_0 |= P1 for all 0 <= i < j, or
      // w^{i.}, L_0 |= P1 for all i.
      if (!property.lhs || !property.rhs) {
        return false;
      }
      for (std::size_t j = 0; j < word.size(); ++j) {
        if (Satisfies(Suffix(word, j), *property.rhs, context)) {
          bool prefix_holds = true;
          for (std::size_t i = 0; i < j; ++i) {
            if (!Satisfies(Suffix(word, i), *property.lhs, context)) {
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
        if (!Satisfies(Suffix(word, i), *property.lhs, context)) {
          return false;
        }
      }
      return true;
    }
    case LvProperty::Kind::kAcceptOn: {
      // §F.5.6.1: w, L_0 |= ( accept_on (b) P ) iff w, L_0 |= P, or for some
      // 0 <= i < |w| with w^i |= b, w^{0,i-1} T^omega, L_0 |= P.
      if (!property.boolean || !property.lhs) {
        return false;
      }
      if (Satisfies(word, *property.lhs, context)) {
        return true;
      }
      const std::size_t reach = PropertyReach(*property.lhs);
      for (std::size_t i = 0; i < word.size(); ++i) {
        if (LetterSatisfiesBoolean(word[i], *property.boolean)) {
          const Word completed =
              PrefixWithTail(FirstLetters(word, i), LetterTop(), reach);
          if (Satisfies(completed, *property.lhs, context)) {
            return true;
          }
        }
      }
      return false;
    }
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
      const std::size_t i = FirstSatisfyingIndex(word, *top.disable_condition);
      if (i == word.size()) {
        return Satisfies(word, *top.property, context);
      }
      const std::size_t reach = PropertyReach(*top.property);
      const Word completed =
          PrefixWithTail(FirstLetters(word, i), LetterBottom(), reach);
      return Satisfies(completed, *top.property, context);
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
    case LvTopLevelProperty::Kind::kDisableIff: {
      // §F.5.6.1: for T = disable iff (b) P, w, L_0 |=^d T iff some letter of w
      // satisfies b and both w^{0,i-1} T^omega, L_0 |= P and
      // w^{0,i-1} _|_^omega, L_0 |/= P for i the least index with w^i |= b.
      if (!top.disable_condition || !top.property) {
        return false;
      }
      const std::size_t i = FirstSatisfyingIndex(word, *top.disable_condition);
      if (i == word.size()) {
        return false;
      }
      const std::size_t reach = PropertyReach(*top.property);
      const Word prefix = FirstLetters(word, i);
      const Word top_completed = PrefixWithTail(prefix, LetterTop(), reach);
      const Word bottom_completed =
          PrefixWithTail(prefix, LetterBottom(), reach);
      return Satisfies(top_completed, *top.property, context) &&
             !Satisfies(bottom_completed, *top.property, context);
    }
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
