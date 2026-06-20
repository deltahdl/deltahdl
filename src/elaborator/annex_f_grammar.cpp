#include "elaborator/annex_f_grammar.h"

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_notation.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

std::shared_ptr<const BooleanExpr> BoolTrue() {
  auto node = std::make_shared<BooleanExpr>();
  node->kind = BooleanExpr::Kind::kTrue;
  return node;
}

std::shared_ptr<const BooleanExpr> BoolAtom(std::string name) {
  auto node = std::make_shared<BooleanExpr>();
  node->kind = BooleanExpr::Kind::kAtom;
  node->atom = std::move(name);
  return node;
}

std::shared_ptr<const BooleanExpr> BoolNot(
    std::shared_ptr<const BooleanExpr> a) {
  auto node = std::make_shared<BooleanExpr>();
  node->kind = BooleanExpr::Kind::kNot;
  node->operand_a = std::move(a);
  return node;
}

std::shared_ptr<const BooleanExpr> BoolAnd(
    std::shared_ptr<const BooleanExpr> a,
    std::shared_ptr<const BooleanExpr> b) {
  auto node = std::make_shared<BooleanExpr>();
  node->kind = BooleanExpr::Kind::kAnd;
  node->operand_a = std::move(a);
  node->operand_b = std::move(b);
  return node;
}

bool BooleanExprEqual(const BooleanExpr& lhs, const BooleanExpr& rhs) {
  if (lhs.kind != rhs.kind) {
    return false;
  }
  switch (lhs.kind) {
    case BooleanExpr::Kind::kTrue:
      return true;
    case BooleanExpr::Kind::kAtom:
      return lhs.atom == rhs.atom;
    case BooleanExpr::Kind::kNot:
      return BooleanExprEqual(*lhs.operand_a, *rhs.operand_a);
    case BooleanExpr::Kind::kAnd:
      return BooleanExprEqual(*lhs.operand_a, *rhs.operand_a) &&
             BooleanExprEqual(*lhs.operand_b, *rhs.operand_b);
  }
  return false;
}

namespace {

std::shared_ptr<SequenceExpr> MakeSequence(SequenceExpr::Kind kind) {
  auto node = std::make_shared<SequenceExpr>();
  node->kind = kind;
  return node;
}

}  // namespace

std::shared_ptr<const SequenceExpr> SeqBoolean(
    std::shared_ptr<const BooleanExpr> b) {
  auto node = MakeSequence(SequenceExpr::Kind::kBoolean);
  node->boolean = std::move(b);
  return node;
}

std::shared_ptr<const SequenceExpr> SeqLocalVarDecl(
    std::string type, std::string name,
    std::shared_ptr<const SequenceExpr> rest) {
  auto node = MakeSequence(SequenceExpr::Kind::kLocalVarDecl);
  node->local_var_type = std::move(type);
  node->local_var_name = std::move(name);
  node->lhs = std::move(rest);
  return node;
}

std::shared_ptr<const SequenceExpr> SeqLocalVarSampling(std::string name) {
  auto node = MakeSequence(SequenceExpr::Kind::kLocalVarSampling);
  node->local_var_name = std::move(name);
  return node;
}

std::shared_ptr<const SequenceExpr> SeqParen(
    std::shared_ptr<const SequenceExpr> inner) {
  auto node = MakeSequence(SequenceExpr::Kind::kParen);
  node->lhs = std::move(inner);
  return node;
}

std::shared_ptr<const SequenceExpr> SeqConcat(
    std::shared_ptr<const SequenceExpr> a,
    std::shared_ptr<const SequenceExpr> b) {
  auto node = MakeSequence(SequenceExpr::Kind::kConcat);
  node->lhs = std::move(a);
  node->rhs = std::move(b);
  return node;
}

std::shared_ptr<const SequenceExpr> SeqFusion(
    std::shared_ptr<const SequenceExpr> a,
    std::shared_ptr<const SequenceExpr> b) {
  auto node = MakeSequence(SequenceExpr::Kind::kFusion);
  node->lhs = std::move(a);
  node->rhs = std::move(b);
  return node;
}

std::shared_ptr<const SequenceExpr> SeqOr(
    std::shared_ptr<const SequenceExpr> a,
    std::shared_ptr<const SequenceExpr> b) {
  auto node = MakeSequence(SequenceExpr::Kind::kOr);
  node->lhs = std::move(a);
  node->rhs = std::move(b);
  return node;
}

std::shared_ptr<const SequenceExpr> SeqIntersect(
    std::shared_ptr<const SequenceExpr> a,
    std::shared_ptr<const SequenceExpr> b) {
  auto node = MakeSequence(SequenceExpr::Kind::kIntersect);
  node->lhs = std::move(a);
  node->rhs = std::move(b);
  return node;
}

std::shared_ptr<const SequenceExpr> SeqFirstMatch(
    std::shared_ptr<const SequenceExpr> inner) {
  auto node = MakeSequence(SequenceExpr::Kind::kFirstMatch);
  node->lhs = std::move(inner);
  return node;
}

std::shared_ptr<const SequenceExpr> SeqNullRepeat(
    std::shared_ptr<const SequenceExpr> inner) {
  auto node = MakeSequence(SequenceExpr::Kind::kNullRepeat);
  node->lhs = std::move(inner);
  return node;
}

std::shared_ptr<const SequenceExpr> SeqUnboundedRepeat(
    std::shared_ptr<const SequenceExpr> inner) {
  auto node = MakeSequence(SequenceExpr::Kind::kUnboundedRepeat);
  node->lhs = std::move(inner);
  return node;
}

std::shared_ptr<const SequenceExpr> SeqZeroOrMoreRepeat(
    std::shared_ptr<const SequenceExpr> inner) {
  auto node = MakeSequence(SequenceExpr::Kind::kZeroOrMoreRepeat);
  node->lhs = std::move(inner);
  return node;
}

std::shared_ptr<const SequenceExpr> SeqClock(
    std::shared_ptr<const BooleanExpr> event,
    std::shared_ptr<const SequenceExpr> inner) {
  auto node = MakeSequence(SequenceExpr::Kind::kClock);
  node->boolean = std::move(event);
  node->rhs = std::move(inner);
  return node;
}

bool SequenceExprEqual(const SequenceExpr& lhs, const SequenceExpr& rhs) {
  if (lhs.kind != rhs.kind) {
    return false;
  }
  auto child_equal = [](const std::shared_ptr<const SequenceExpr>& a,
                        const std::shared_ptr<const SequenceExpr>& b) {
    if (a == nullptr || b == nullptr) {
      return a == b;
    }
    return SequenceExprEqual(*a, *b);
  };
  auto bool_equal = [](const std::shared_ptr<const BooleanExpr>& a,
                       const std::shared_ptr<const BooleanExpr>& b) {
    if (a == nullptr || b == nullptr) {
      return a == b;
    }
    return BooleanExprEqual(*a, *b);
  };
  return bool_equal(lhs.boolean, rhs.boolean) &&
         child_equal(lhs.lhs, rhs.lhs) && child_equal(lhs.rhs, rhs.rhs) &&
         lhs.local_var_type == rhs.local_var_type &&
         lhs.local_var_name == rhs.local_var_name;
}

bool ContainsClock(const SequenceExpr& seq) {
  if (seq.kind == SequenceExpr::Kind::kClock) {
    return true;
  }
  if (seq.lhs != nullptr && ContainsClock(*seq.lhs)) {
    return true;
  }
  if (seq.rhs != nullptr && ContainsClock(*seq.rhs)) {
    return true;
  }
  return false;
}

NotationCategory CategoryOfProduction(GrammarProduction production) {
  switch (production) {
    case GrammarProduction::kUnclockedSequence:
      return NotationCategory::kUnclockedSequence;
    case GrammarProduction::kClockedSequence:
      return NotationCategory::kClockedSequence;
    case GrammarProduction::kUnclockedProperty:
      return NotationCategory::kUnclockedProperty;
    case GrammarProduction::kClockedProperty:
      return NotationCategory::kClockedProperty;
    case GrammarProduction::kUnclockedTopLevelProperty:
      return NotationCategory::kUnclockedTopLevelProperty;
    case GrammarProduction::kClockedTopLevelProperty:
      return NotationCategory::kClockedTopLevelProperty;
    case GrammarProduction::kAssertion:
      return NotationCategory::kAssertion;
  }
  return NotationCategory::kAssertion;
}

std::vector<GrammarForm> ProductionForms(GrammarProduction production) {
  switch (production) {
    case GrammarProduction::kUnclockedSequence:
      return {
          {"boolean", {"b"}},
          {"local variable declaration", {"t", "v", "e", "R"}},
          {"local variable sampling", {"v", "e"}},
          {"parenthesis", {"R"}},
          {"concatenation", {"R", "R"}},
          {"fusion", {"R", "R"}},
          {"or", {"R", "R"}},
          {"intersect", {"R", "R"}},
          {"first match", {"R"}},
          {"null repetition", {"R"}},
          {"unbounded repetition", {"R"}},
      };
    case GrammarProduction::kClockedSequence:
      return {
          {"clock", {"b", "R"}},
          {"local variable declaration", {"t", "v", "e", "S"}},
          {"parenthesized", {"S"}},
          {"concatenation", {"S", "S"}},
      };
    case GrammarProduction::kUnclockedProperty:
      return {
          {"strong sequence", {"R"}},
          {"weak sequence", {"R"}},
          {"local variable declaration", {"t", "v", "e", "P"}},
          {"parenthesis", {"P"}},
          {"negation", {"P"}},
          {"or", {"P", "P"}},
          {"and", {"P", "P"}},
          {"implication", {"R", "P"}},
          {"nexttime", {"P"}},
          {"until", {"P", "P"}},
          {"abort", {"b", "P"}},
      };
    case GrammarProduction::kClockedProperty:
      return {
          {"clock", {"b", "P"}},
          {"strong sequence", {"S"}},
          {"weak sequence", {"S"}},
          {"local variable declaration", {"t", "v", "e", "Q"}},
          {"parenthesis", {"Q"}},
          {"negation", {"Q"}},
          {"or", {"Q", "Q"}},
          {"and", {"Q", "Q"}},
          {"implication", {"S", "Q"}},
          {"nexttime", {"Q"}},
          {"until", {"Q", "Q"}},
          {"abort", {"b", "Q"}},
      };
    case GrammarProduction::kUnclockedTopLevelProperty:
      return {
          {"plain", {"P"}},
          {"disable", {"b", "P"}},
          {"local variable declaration", {"t", "v", "e", "T"}},
          {"parenthesis", {"T"}},
      };
    case GrammarProduction::kClockedTopLevelProperty:
      return {
          {"plain", {"Q"}},
          {"disable", {"b", "Q"}},
          {"local variable declaration", {"t", "v", "e", "U"}},
          {"parenthesis", {"U"}},
      };
    case GrammarProduction::kAssertion:
      return {
          {"always", {"U"}},
          {"always with clock", {"b", "T"}},
          {"initial", {"U"}},
          {"initial with clock", {"b", "T"}},
      };
  }
  return {};
}

bool SequenceOperandSatisfiesNondegeneracyRequirement(const SequenceExpr& seq) {
  // §F.3.2 imposes two conditions on the sequence operand of a strong/weak
  // sequence property: it shall be nondegenerate, and it shall not be tightly
  // satisfied by the empty word. Both definitions live in §F.5.2.
  return IsNondegenerateSequence(seq) && !TightlySatisfiedByEmptyWord(seq);
}

}  // namespace delta
