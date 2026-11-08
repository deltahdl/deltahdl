#pragma once

#include <cstddef>
#include <cstdint>
#include <memory>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

struct PropertyExpr {
  enum class Kind : std::uint8_t {
    kStrong,
    kWeak,
    kParen,
    kNot,
    kImplication,
    kOr,
    kAnd,
    kNexttime,
    kUntil,
    kAcceptOn,
  };

  Kind kind = Kind::kStrong;
  std::shared_ptr<const SequenceExpr> sequence;
  std::shared_ptr<const BooleanExpr> boolean;
  std::shared_ptr<const PropertyExpr> lhs;
  std::shared_ptr<const PropertyExpr> rhs;
};

std::shared_ptr<const PropertyExpr> PropStrong(
    std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const PropertyExpr> PropWeak(
    std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const PropertyExpr> PropParen(
    std::shared_ptr<const PropertyExpr> inner);
std::shared_ptr<const PropertyExpr> PropNot(
    std::shared_ptr<const PropertyExpr> inner);
std::shared_ptr<const PropertyExpr> PropImplication(
    std::shared_ptr<const SequenceExpr> antecedent,
    std::shared_ptr<const PropertyExpr> consequent);
std::shared_ptr<const PropertyExpr> PropOr(
    std::shared_ptr<const PropertyExpr> a,
    std::shared_ptr<const PropertyExpr> b);
std::shared_ptr<const PropertyExpr> PropAnd(
    std::shared_ptr<const PropertyExpr> a,
    std::shared_ptr<const PropertyExpr> b);
std::shared_ptr<const PropertyExpr> PropNexttime(
    std::shared_ptr<const PropertyExpr> inner);
std::shared_ptr<const PropertyExpr> PropUntil(
    std::shared_ptr<const PropertyExpr> a,
    std::shared_ptr<const PropertyExpr> b);
std::shared_ptr<const PropertyExpr> PropAcceptOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> inner);

struct TopLevelProperty {
  enum class Kind : std::uint8_t {
    kProperty,
    kDisableIff,
    kParen,
  };

  Kind kind = Kind::kProperty;
  std::shared_ptr<const BooleanExpr> disable_condition;
  std::shared_ptr<const PropertyExpr> property;
  std::shared_ptr<const TopLevelProperty> inner;
};

std::shared_ptr<const TopLevelProperty> TopProperty(
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const TopLevelProperty> TopDisableIff(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const TopLevelProperty> TopParen(
    std::shared_ptr<const TopLevelProperty> inner);

bool NeutrallySatisfies(const Word& word, const PropertyExpr& property);

bool NeutrallySatisfiesTopLevel(const Word& word, const TopLevelProperty& top);

bool DisablesTopLevel(const Word& word, const TopLevelProperty& top);

bool PassesTopLevel(const Word& word, const TopLevelProperty& top);
bool IsDisabledTopLevel(const Word& word, const TopLevelProperty& top);
bool FailsTopLevel(const Word& word, const TopLevelProperty& top);

bool NeutrallySatisfiesClockedProperty(const Word& word,
                                       const ClockedProperty& q);

struct ClockedTopLevelProperty {
  enum class Kind : std::uint8_t {
    kProperty,
    kDisableIff,
    kParen,
  };

  Kind kind = Kind::kProperty;
  std::shared_ptr<const BooleanExpr> disable_condition;
  std::shared_ptr<const ClockedProperty> property;
  std::shared_ptr<const ClockedTopLevelProperty> inner;
};

std::shared_ptr<const ClockedTopLevelProperty> ClockedTopProperty(
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const ClockedTopLevelProperty> ClockedTopDisableIff(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const ClockedTopLevelProperty> ClockedTopParen(
    std::shared_ptr<const ClockedTopLevelProperty> inner);

std::shared_ptr<const PropertyExpr> UnclockedPropertyOf(
    const ClockedProperty& q, const std::shared_ptr<const BooleanExpr>& clock);

bool NeutrallySatisfiesTopLevelClocked(const Word& word,
                                       const ClockedTopLevelProperty& top);
bool DisablesTopLevelClocked(const Word& word,
                             const ClockedTopLevelProperty& top);

bool PassesTopLevelClocked(const Word& word,
                           const ClockedTopLevelProperty& top);
bool IsDisabledTopLevelClocked(const Word& word,
                               const ClockedTopLevelProperty& top);
bool FailsTopLevelClocked(const Word& word, const ClockedTopLevelProperty& top);

struct AssertionStatement {
  enum class Activation : std::uint8_t { kAlways, kInitial };
  enum class Role : std::uint8_t { kAssert, kAssume, kCover };
  enum class Form : std::uint8_t {
    kExplicitClock,
    kClockedTop,
  };

  Activation activation = Activation::kAlways;
  Role role = Role::kAssert;
  Form form = Form::kExplicitClock;
  std::shared_ptr<const BooleanExpr> clock;
  std::shared_ptr<const TopLevelProperty> top;
  std::shared_ptr<const ClockedTopLevelProperty> clocked_top;
};

struct AssertionActivation {
  AssertionStatement::Activation activation =
      AssertionStatement::Activation::kAlways;
  AssertionStatement::Form form = AssertionStatement::Form::kExplicitClock;
  std::shared_ptr<const BooleanExpr> clock;
};
AssertionActivation ActivationOf(const AssertionStatement& assertion);

bool ActivationPointEnabled(std::size_t i, const Word& complement,
                            const BooleanExpr& enabling,
                            const AssertionActivation& activation);

std::shared_ptr<const AssertionStatement> AssertionWithClock(
    AssertionStatement::Activation activation, AssertionStatement::Role role,
    std::shared_ptr<const BooleanExpr> clock,
    std::shared_ptr<const TopLevelProperty> top);
std::shared_ptr<const AssertionStatement> AssertionWithClockedTop(
    AssertionStatement::Activation activation, AssertionStatement::Role role,
    std::shared_ptr<const ClockedTopLevelProperty> clocked_top);

bool NeutrallySatisfiesAssertion(const Word& word, const BooleanExpr& enabling,
                                 const AssertionStatement& assertion);

bool NeutrallySatisfiesAssertionWithTail(const Word& word, const Letter& tail,
                                         const BooleanExpr& enabling,
                                         const AssertionStatement& assertion);

struct EnabledAssertion {
  AssertionStatement statement;
  std::shared_ptr<const BooleanExpr> enabling;
};

bool WordIsFeasible(const Word& word,
                    const std::vector<EnabledAssertion>& assumptions);

bool AssertSatisfiedOnWordSet(const EnabledAssertion& assertion,
                              const std::vector<Word>& words,
                              const std::vector<EnabledAssertion>& assumptions);

bool CoverSatisfiedOnWordSet(const EnabledAssertion& assertion,
                             const std::vector<Word>& words,
                             const std::vector<EnabledAssertion>& assumptions);

bool HoldsGloballyOnWordSet(const EnabledAssertion& assertion,
                            const std::vector<Word>& words,
                            const std::vector<EnabledAssertion>& assumptions);

}  // namespace delta
