#pragma once

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "elaborator/annex_f_notation.h"

namespace delta {

struct BooleanExpr {
  enum class Kind : std::uint8_t {
    kTrue,
    kAtom,
    kNot,
    kAnd,
  };

  Kind kind = Kind::kTrue;
  std::string atom;
  std::shared_ptr<const BooleanExpr> operand_a;
  std::shared_ptr<const BooleanExpr> operand_b;
};

std::shared_ptr<const BooleanExpr> BoolTrue();
std::shared_ptr<const BooleanExpr> BoolAtom(std::string name);
std::shared_ptr<const BooleanExpr> BoolNot(
    std::shared_ptr<const BooleanExpr> a);
std::shared_ptr<const BooleanExpr> BoolAnd(
    std::shared_ptr<const BooleanExpr> a, std::shared_ptr<const BooleanExpr> b);

bool BooleanExprEqual(const BooleanExpr& lhs, const BooleanExpr& rhs);

struct SequenceExpr {
  enum class Kind : std::uint8_t {
    kBoolean,
    kLocalVarDecl,
    kLocalVarSampling,
    kParen,
    kConcat,
    kFusion,
    kOr,
    kIntersect,
    kFirstMatch,
    kNullRepeat,
    kUnboundedRepeat,
    kClock,
    kZeroOrMoreRepeat,
  };

  Kind kind = Kind::kBoolean;
  std::shared_ptr<const BooleanExpr> boolean;
  std::shared_ptr<const SequenceExpr> lhs;
  std::shared_ptr<const SequenceExpr> rhs;
  std::string local_var_type;
  std::string local_var_name;
};

std::shared_ptr<const SequenceExpr> SeqBoolean(
    std::shared_ptr<const BooleanExpr> b);
std::shared_ptr<const SequenceExpr> SeqLocalVarDecl(
    std::string type, std::string name,
    std::shared_ptr<const SequenceExpr> rest);
std::shared_ptr<const SequenceExpr> SeqLocalVarSampling(std::string name);
std::shared_ptr<const SequenceExpr> SeqParen(
    std::shared_ptr<const SequenceExpr> inner);
std::shared_ptr<const SequenceExpr> SeqConcat(
    std::shared_ptr<const SequenceExpr> a,
    std::shared_ptr<const SequenceExpr> b);
std::shared_ptr<const SequenceExpr> SeqFusion(
    std::shared_ptr<const SequenceExpr> a,
    std::shared_ptr<const SequenceExpr> b);
std::shared_ptr<const SequenceExpr> SeqOr(
    std::shared_ptr<const SequenceExpr> a,
    std::shared_ptr<const SequenceExpr> b);
std::shared_ptr<const SequenceExpr> SeqIntersect(
    std::shared_ptr<const SequenceExpr> a,
    std::shared_ptr<const SequenceExpr> b);
std::shared_ptr<const SequenceExpr> SeqFirstMatch(
    std::shared_ptr<const SequenceExpr> inner);
std::shared_ptr<const SequenceExpr> SeqNullRepeat(
    std::shared_ptr<const SequenceExpr> inner);
std::shared_ptr<const SequenceExpr> SeqUnboundedRepeat(
    std::shared_ptr<const SequenceExpr> inner);
std::shared_ptr<const SequenceExpr> SeqZeroOrMoreRepeat(
    std::shared_ptr<const SequenceExpr> inner);
std::shared_ptr<const SequenceExpr> SeqClock(
    std::shared_ptr<const BooleanExpr> event,
    std::shared_ptr<const SequenceExpr> inner);

bool SequenceExprEqual(const SequenceExpr& lhs, const SequenceExpr& rhs);

bool ContainsClock(const SequenceExpr& seq);

enum class GrammarProduction : std::uint8_t {
  kUnclockedSequence,
  kClockedSequence,
  kUnclockedProperty,
  kClockedProperty,
  kUnclockedTopLevelProperty,
  kClockedTopLevelProperty,
  kAssertion,
};

NotationCategory CategoryOfProduction(GrammarProduction production);

struct GrammarForm {
  std::string label;
  std::vector<std::string> operands;
};

std::vector<GrammarForm> ProductionForms(GrammarProduction production);

bool SequenceOperandSatisfiesNondegeneracyRequirement(const SequenceExpr& seq);

}  // namespace delta
