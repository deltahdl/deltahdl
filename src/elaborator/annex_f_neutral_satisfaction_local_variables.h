#pragma once

#include <cstdint>
#include <memory>
#include <string>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

namespace delta {

struct LvProperty {
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
    kLocalVarDecl,
  };

  Kind kind = Kind::kStrong;
  std::shared_ptr<const SequenceExpr> sequence;
  std::shared_ptr<const BooleanExpr> boolean;
  std::shared_ptr<const LvProperty> lhs;
  std::shared_ptr<const LvProperty> rhs;
  std::string local_var_type;
  std::string local_var_name;
};

std::shared_ptr<const LvProperty> LvStrong(
    std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const LvProperty> LvWeak(std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const LvProperty> LvParen(
    std::shared_ptr<const LvProperty> inner);
std::shared_ptr<const LvProperty> LvNot(
    std::shared_ptr<const LvProperty> inner);
std::shared_ptr<const LvProperty> LvImplication(
    std::shared_ptr<const SequenceExpr> antecedent,
    std::shared_ptr<const LvProperty> consequent);
std::shared_ptr<const LvProperty> LvOr(std::shared_ptr<const LvProperty> a,
                                       std::shared_ptr<const LvProperty> b);
std::shared_ptr<const LvProperty> LvAnd(std::shared_ptr<const LvProperty> a,
                                        std::shared_ptr<const LvProperty> b);
std::shared_ptr<const LvProperty> LvNexttime(
    std::shared_ptr<const LvProperty> inner);
std::shared_ptr<const LvProperty> LvUntil(std::shared_ptr<const LvProperty> a,
                                          std::shared_ptr<const LvProperty> b);
std::shared_ptr<const LvProperty> LvAcceptOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const LvProperty> inner);
std::shared_ptr<const LvProperty> LvLocalVarDecl(
    std::string type, std::string name, std::shared_ptr<const LvProperty> body);

struct LvTopLevelProperty {
  enum class Kind : std::uint8_t {
    kProperty,
    kDisableIff,
    kParen,
    kLocalVarDecl,
  };

  Kind kind = Kind::kProperty;
  std::shared_ptr<const BooleanExpr> disable_condition;
  std::shared_ptr<const LvProperty> property;
  std::shared_ptr<const LvTopLevelProperty> inner;
  std::string local_var_type;
  std::string local_var_name;
};

std::shared_ptr<const LvTopLevelProperty> LvTopProperty(
    std::shared_ptr<const LvProperty> p);
std::shared_ptr<const LvTopLevelProperty> LvTopDisableIff(
    std::shared_ptr<const BooleanExpr> b, std::shared_ptr<const LvProperty> p);
std::shared_ptr<const LvTopLevelProperty> LvTopParen(
    std::shared_ptr<const LvTopLevelProperty> inner);
std::shared_ptr<const LvTopLevelProperty> LvTopLocalVarDecl(
    std::string type, std::string name,
    std::shared_ptr<const LvTopLevelProperty> body);

bool NeutrallySatisfiesWithLocals(const Word& word, const LvProperty& property,
                                  const LocalContext& context);

bool NeutrallySatisfiesWithLocals(const Word& word, const LvProperty& property);

bool NeutrallySatisfiesTopLevelWithLocals(const Word& word,
                                          const LvTopLevelProperty& top,
                                          const LocalContext& context);

bool DisablesTopLevelWithLocals(const Word& word, const LvTopLevelProperty& top,
                                const LocalContext& context);

bool PassesTopLevelWithLocals(const Word& word, const LvTopLevelProperty& top,
                              const LocalContext& context);
bool IsDisabledTopLevelWithLocals(const Word& word,
                                  const LvTopLevelProperty& top,
                                  const LocalContext& context);
bool FailsTopLevelWithLocals(const Word& word, const LvTopLevelProperty& top,
                             const LocalContext& context);

}  // namespace delta
