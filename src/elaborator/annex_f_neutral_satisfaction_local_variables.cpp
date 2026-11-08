#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"

#include <cstddef>
#include <memory>
#include <string>
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

bool UntilLhsHoldsThroughLimit(const Word& word, const LvProperty& lhs,
                               const LocalContext& context, std::size_t limit) {
  for (std::size_t i = 0; i < limit; ++i) {
    if (!Satisfies(Suffix(word, i), lhs, context)) {
      return false;
    }
  }
  return true;
}

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
      return property.lhs &&
             Satisfies(word, *property.lhs,
                       RemoveName(context, property.local_var_name));
    case LvProperty::Kind::kParen:
      return property.lhs && Satisfies(word, *property.lhs, context);
    case LvProperty::Kind::kNot:
      return property.lhs &&
             !Satisfies(ComplementWord(word), *property.lhs, context);
    case LvProperty::Kind::kStrong:
      return property.sequence &&
             StrongHolds(word, *property.sequence, context);
    case LvProperty::Kind::kWeak:
      return property.sequence && WeakHolds(word, *property.sequence, context);
    case LvProperty::Kind::kImplication:
      return ImplicationHolds(word, property, context);
    case LvProperty::Kind::kOr:
      return (property.lhs && Satisfies(word, *property.lhs, context)) ||
             (property.rhs && Satisfies(word, *property.rhs, context));
    case LvProperty::Kind::kAnd:
      return property.lhs && property.rhs &&
             Satisfies(word, *property.lhs, context) &&
             Satisfies(word, *property.rhs, context);
    case LvProperty::Kind::kNexttime:
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
  return Satisfies(word, property, LocalContext{});
}

bool NeutrallySatisfiesTopLevelWithLocals(const Word& word,
                                          const LvTopLevelProperty& top,
                                          const LocalContext& context) {
  switch (top.kind) {
    case LvTopLevelProperty::Kind::kProperty:
      return top.property && Satisfies(word, *top.property, context);
    case LvTopLevelProperty::Kind::kDisableIff: {
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
      return top.inner &&
             NeutrallySatisfiesTopLevelWithLocals(word, *top.inner, context);
    case LvTopLevelProperty::Kind::kLocalVarDecl:
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
      return false;
    case LvTopLevelProperty::Kind::kDisableIff:
      return DisableIffShape(word, top,
                             [&context](const Word& w, const auto& p) {
                               return Satisfies(w, p, context);
                             });
    case LvTopLevelProperty::Kind::kParen:
      return top.inner && DisablesTopLevelWithLocals(word, *top.inner, context);
    case LvTopLevelProperty::Kind::kLocalVarDecl:
      return top.inner &&
             DisablesTopLevelWithLocals(
                 word, *top.inner, RemoveName(context, top.local_var_name));
  }
  return false;
}

bool PassesTopLevelWithLocals(const Word& word, const LvTopLevelProperty& top,
                              const LocalContext& context) {
  return NeutrallySatisfiesTopLevelWithLocals(word, top, context);
}

bool IsDisabledTopLevelWithLocals(const Word& word,
                                  const LvTopLevelProperty& top,
                                  const LocalContext& context) {
  return DisablesTopLevelWithLocals(word, top, context);
}

bool FailsTopLevelWithLocals(const Word& word, const LvTopLevelProperty& top,
                             const LocalContext& context) {
  return !PassesTopLevelWithLocals(word, top, context) &&
         !IsDisabledTopLevelWithLocals(word, top, context);
}

}  // namespace delta
