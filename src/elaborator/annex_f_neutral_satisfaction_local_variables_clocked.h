#pragma once

#include <cstdint>
#include <memory>
#include <string>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

namespace delta {

bool NeutrallySatisfiesClockedPropertyWithLocals(const Word& word,
                                                 const ClockedProperty& q,
                                                 const LocalContext& context);

struct LvClockedTopLevelProperty {
  enum class Kind : std::uint8_t {
    kProperty,
    kDisableIff,
    kParen,
    kLocalVarDecl,
  };

  Kind kind = Kind::kProperty;
  std::shared_ptr<const BooleanExpr> disable_condition;
  std::shared_ptr<const ClockedProperty> property;
  std::shared_ptr<const LvClockedTopLevelProperty> inner;
  std::string local_var_type;
  std::string local_var_name;
};

std::shared_ptr<const LvClockedTopLevelProperty> LvClockedTopProperty(
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const LvClockedTopLevelProperty> LvClockedTopDisableIff(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const LvClockedTopLevelProperty> LvClockedTopParen(
    std::shared_ptr<const LvClockedTopLevelProperty> inner);
std::shared_ptr<const LvClockedTopLevelProperty> LvClockedTopLocalVarDecl(
    std::string type, std::string name,
    std::shared_ptr<const LvClockedTopLevelProperty> body);

std::shared_ptr<const LvTopLevelProperty> UnclockTopLevelWithLocals(
    const LvClockedTopLevelProperty& top,
    const std::shared_ptr<const BooleanExpr>& clock);

bool NeutrallySatisfiesTopLevelClockedWithLocals(
    const Word& word, const LvClockedTopLevelProperty& top,
    const LocalContext& context);
bool DisablesTopLevelClockedWithLocals(const Word& word,
                                       const LvClockedTopLevelProperty& top,
                                       const LocalContext& context);
bool PassesTopLevelClockedWithLocals(const Word& word,
                                     const LvClockedTopLevelProperty& top,
                                     const LocalContext& context);
bool IsDisabledTopLevelClockedWithLocals(const Word& word,
                                         const LvClockedTopLevelProperty& top,
                                         const LocalContext& context);
bool FailsTopLevelClockedWithLocals(const Word& word,
                                    const LvClockedTopLevelProperty& top,
                                    const LocalContext& context);

struct LvAssertionStatement {
  AssertionStatement::Activation activation =
      AssertionStatement::Activation::kAlways;
  AssertionStatement::Role role = AssertionStatement::Role::kAssert;
  AssertionStatement::Form form = AssertionStatement::Form::kExplicitClock;
  std::shared_ptr<const BooleanExpr> clock;
  std::shared_ptr<const LvClockedTopLevelProperty> body;
};

std::shared_ptr<const LvAssertionStatement> LvAssertionWithClock(
    AssertionStatement::Activation activation, AssertionStatement::Role role,
    std::shared_ptr<const BooleanExpr> clock,
    std::shared_ptr<const LvClockedTopLevelProperty> top);
std::shared_ptr<const LvAssertionStatement> LvAssertionWithClockedTop(
    AssertionStatement::Activation activation, AssertionStatement::Role role,
    std::shared_ptr<const LvClockedTopLevelProperty> clocked_top);

bool NeutrallySatisfiesAssertionWithLocals(
    const Word& word, const BooleanExpr& enabling,
    const LvAssertionStatement& assertion);

bool NeutrallySatisfiesAssertionWithLocalsWithTail(
    const Word& word, const Letter& tail, const BooleanExpr& enabling,
    const LvAssertionStatement& assertion);

}  // namespace delta
