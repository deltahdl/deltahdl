#include "parser/parser_property_grammar.h"

#include <algorithm>
#include <array>
#include <cstdint>
#include <initializer_list>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"
#include "parser/parser_token_skips.h"

namespace delta {

namespace {

enum class Kind : uint8_t { kBoolean, kSequence, kInstance, kProperty };

bool Fits(Kind kind, Kind most) {
  return kind == Kind::kInstance || kind <= most;
}

enum class Operands : uint8_t {
  kSequences,
  kBooleanSequence,
  kEither,
  kSequenceProperty,
  kProperties,
};

struct JoinForm {
  TokenKind kind;
  int precedence;
  bool right;
  Operands operands;
};

constexpr std::array<JoinForm, 16> kJoins = {{
    {TokenKind::kHashHash, 9, false, Operands::kSequences},
    {TokenKind::kKwThroughout, 8, true, Operands::kBooleanSequence},
    {TokenKind::kKwWithin, 7, false, Operands::kSequences},
    {TokenKind::kKwIntersect, 6, false, Operands::kSequences},
    {TokenKind::kKwAnd, 4, false, Operands::kEither},
    {TokenKind::kKwOr, 3, false, Operands::kEither},
    {TokenKind::kKwIff, 2, true, Operands::kProperties},
    {TokenKind::kKwUntil, 1, true, Operands::kProperties},
    {TokenKind::kKwSUntil, 1, true, Operands::kProperties},
    {TokenKind::kKwUntilWith, 1, true, Operands::kProperties},
    {TokenKind::kKwSUntilWith, 1, true, Operands::kProperties},
    {TokenKind::kKwImplies, 1, true, Operands::kProperties},
    {TokenKind::kPipeDashGt, 0, true, Operands::kSequenceProperty},
    {TokenKind::kPipeEqGt, 0, true, Operands::kSequenceProperty},
    {TokenKind::kHashMinusHash, 0, true, Operands::kSequenceProperty},
    {TokenKind::kHashEqHash, 0, true, Operands::kSequenceProperty},
}};

constexpr int kNotPrecedence = 5;

const JoinForm* FindJoin(TokenKind kind, bool sequence) {
  auto found = std::find_if(
      kJoins.begin(), kJoins.end(), [kind, sequence](const JoinForm& join) {
        return join.kind == kind &&
               (!sequence || join.operands < Operands::kSequenceProperty);
      });
  return found == kJoins.end() ? nullptr : &*found;
}

bool IsJoin(TokenKind kind, bool sequence) {
  return FindJoin(kind, sequence) != nullptr;
}

enum class Bounds : uint8_t { kSingle, kRange, kEither };

enum class Opener : uint8_t {
  kNone,
  kOptionalBracket,
  kBracket,
  kCondition,
  kStrength,
  kFirstMatch,
  kIf,
  kCase,
};

struct PrefixForm {
  TokenKind kind;
  Opener opener;
  Bounds bounds;
  bool dollar;
  bool property;
  bool lowest;
};

constexpr std::array<PrefixForm, 16> kPrefixForms = {{
    {TokenKind::kKwNot, Opener::kNone, Bounds::kSingle, false, true, false},
    {TokenKind::kKwNexttime, Opener::kOptionalBracket, Bounds::kSingle, false,
     true, false},
    {TokenKind::kKwSNexttime, Opener::kOptionalBracket, Bounds::kSingle, false,
     true, false},
    {TokenKind::kKwAlways, Opener::kOptionalBracket, Bounds::kRange, true, true,
     true},
    {TokenKind::kKwSEventually, Opener::kOptionalBracket, Bounds::kRange, true,
     true, true},
    {TokenKind::kKwSAlways, Opener::kBracket, Bounds::kRange, false, true,
     true},
    {TokenKind::kKwEventually, Opener::kBracket, Bounds::kRange, false, true,
     true},
    {TokenKind::kKwAcceptOn, Opener::kCondition, Bounds::kSingle, false, true,
     true},
    {TokenKind::kKwRejectOn, Opener::kCondition, Bounds::kSingle, false, true,
     true},
    {TokenKind::kKwSyncAcceptOn, Opener::kCondition, Bounds::kSingle, false,
     true, true},
    {TokenKind::kKwSyncRejectOn, Opener::kCondition, Bounds::kSingle, false,
     true, true},
    {TokenKind::kKwStrong, Opener::kStrength, Bounds::kSingle, false, true,
     true},
    {TokenKind::kKwWeak, Opener::kStrength, Bounds::kSingle, false, true, true},
    {TokenKind::kKwFirstMatch, Opener::kFirstMatch, Bounds::kSingle, false,
     false, true},
    {TokenKind::kKwIf, Opener::kIf, Bounds::kSingle, false, true, true},
    {TokenKind::kKwCase, Opener::kCase, Bounds::kSingle, false, true, true},
}};

const PrefixForm* FindPrefixForm(TokenKind kind, bool sequence) {
  auto found =
      std::find_if(kPrefixForms.begin(), kPrefixForms.end(),
                   [kind, sequence](const PrefixForm& form) {
                     return form.kind == kind && !(sequence && form.property);
                   });
  return found == kPrefixForms.end() ? nullptr : &*found;
}

constexpr std::array<TokenKind, 7> kOperandEnds = {
    TokenKind::kRParen,       TokenKind::kComma,  TokenKind::kSemicolon,
    TokenKind::kHashHash,     TokenKind::kKwElse, TokenKind::kKwEndsequence,
    TokenKind::kKwEndproperty};

constexpr std::array<TokenKind, 4> kRepetitionOpeners = {
    TokenKind::kStar, TokenKind::kArrow, TokenKind::kEq, TokenKind::kPlus};

constexpr std::array<TokenKind, 3> kEdges = {
    TokenKind::kKwPosedge, TokenKind::kKwNegedge, TokenKind::kKwEdge};

bool IsMatchItemExpr(const Expr& expr) {
  if (expr.kind == ExprKind::kCall || expr.kind == ExprKind::kSystemCall ||
      expr.kind == ExprKind::kPostfixUnary ||
      expr.kind == ExprKind::kIdentifier ||
      expr.kind == ExprKind::kMemberAccess) {
    return true;
  }
  return expr.kind == ExprKind::kUnary &&
         (expr.op == TokenKind::kPlusPlus || expr.op == TokenKind::kMinusMinus);
}

uint64_t Order(SourceLoc loc) {
  return (uint64_t{loc.line} << 32) | loc.column;
}

struct Group {
  bool sequence;
  bool match_items;
  bool sequence_only;
};

enum class Reading : uint8_t { kExpression, kExpressionOrDist, kPrimary };

}  // namespace

class ParserPropertyGrammar::Scan {
 public:
  Scan(Parser& p, bool sequence, bool body)
      : p_(p), sequence_(sequence), body_(body) {}

  bool Spec() {
    if (!SpecChain()) return false;
    if (p_.Check(TokenKind::kRParen)) return true;
    return Fail();
  }

  bool Body(TokenKind end) {
    Kind kind = Kind::kBoolean;
    if (sequence_ ? !Chain(true, kind) : !SpecChain()) return false;
    p_.Match(TokenKind::kSemicolon);
    if (p_.Check(end)) return true;
    return Fail();
  }

  void Report() const {
    if (misplaced_ != nullptr) {
      p_.diag_.Error(misplaced_at_, misplaced_, Subclause("A.2.10"));
      return;
    }
    p_.diag_.Error(furthest_,
                   body_ ? "this declaration's body is not one the grammar "
                           "admits: no reading of it gets past this point"
                         : "this concurrent assertion's spec is not one the "
                           "grammar admits: no reading of it gets past this "
                           "point",
                   Subclause("A.2.10"));
  }

 private:
  bool FailAt(SourceLoc loc) {
    if (Order(loc) > Order(furthest_)) furthest_ = loc;
    return false;
  }

  bool Fail() { return FailAt(p_.CurrentToken().loc); }

  bool Require(Kind kind, Kind most, SourceLoc at) {
    if (Fits(kind, most)) return true;
    misplaced_at_ = at;
    misplaced_ = most == Kind::kBoolean
                     ? "a sequence stands where the grammar admits only an "
                       "expression_or_dist"
                     : "a property stands where the grammar admits only a "
                       "sequence";
    return false;
  }

  bool Expect(TokenKind kind) {
    if (p_.Match(kind)) return true;
    return Fail();
  }

  bool Clean(uint32_t errors) {
    if (p_.diag_.SuppressedErrorCount() == errors) return true;
    return FailAt(p_.diag_.LastSuppressedErrorLoc());
  }

  Expr* Read(Reading reading) {
    const uint32_t kErrors = p_.diag_.SuppressedErrorCount();
    Expr* expr = nullptr;
    switch (reading) {
      case Reading::kExpressionOrDist:
        expr = ParserPropertySpecHelpers::ParseExpressionOrDist(p_);
        break;
      case Reading::kPrimary:
        expr = p_.ParsePrimaryExpr();
        break;
      default:
        expr = p_.ParseExpr();
        break;
    }
    if (!Clean(kErrors)) return nullptr;
    if (expr == nullptr) Fail();
    return expr;
  }

  bool Expression(Reading reading) { return Read(reading) != nullptr; }

  bool SpecChain() {
    if (p_.Check(TokenKind::kAt) && !ClockingEvent()) return false;
    if (p_.Match(TokenKind::kKwDisable) && !DisableIff()) return false;
    Kind kind = Kind::kBoolean;
    return Chain(sequence_, kind);
  }

  bool DisableIff() { return Expect(TokenKind::kKwIff) && Condition(); }

  bool Condition() {
    if (!p_.Match(TokenKind::kLParen)) return Fail();
    return Expression(Reading::kExpressionOrDist) && Expect(TokenKind::kRParen);
  }

  bool Chain(bool sequence, Kind& kind) { return Climb(sequence, 0, kind); }

  bool Climb(bool sequence, int lowest, Kind& kind) {
    const SourceLoc kAt = p_.CurrentToken().loc;
    if (!Operand(sequence, kind)) return false;
    for (;;) {
      const JoinForm* join = FindJoin(p_.CurrentToken().kind, sequence);
      if (join == nullptr || join->precedence < lowest) return true;
      if (!TakesLeft(*join, kind, kAt) || !Operator(*join)) return false;
      const SourceLoc kRightAt = p_.CurrentToken().loc;
      Kind right = Kind::kBoolean;
      const int kNext = join->right ? join->precedence : join->precedence + 1;
      if (!Climb(sequence, kNext, right) ||
          !TakesRight(*join, kind, right, kRightAt)) {
        return false;
      }
    }
  }

  bool Operator(const JoinForm& join) {
    if (join.kind == TokenKind::kHashHash) return CycleDelay();
    p_.Consume();
    return true;
  }

  bool TakesLeft(const JoinForm& join, Kind left, SourceLoc at) {
    switch (join.operands) {
      case Operands::kBooleanSequence:
        return Require(left, Kind::kBoolean, at);
      case Operands::kSequences:
      case Operands::kSequenceProperty:
        return Require(left, Kind::kSequence, at);
      default:
        return true;
    }
  }

  bool TakesRight(const JoinForm& join, Kind& left, Kind right, SourceLoc at) {
    switch (join.operands) {
      case Operands::kSequences:
      case Operands::kBooleanSequence:
        left = Kind::kSequence;
        return Require(right, Kind::kSequence, at);
      case Operands::kEither:
        left = std::max({left, right, Kind::kSequence});
        return true;
      default:
        left = Kind::kProperty;
        return true;
    }
  }

  bool Operand(bool sequence, Kind& kind) {
    if (p_.Check(TokenKind::kHashHash)) {
      if (!CycleDelay()) return false;
      const SourceLoc kAt = p_.CurrentToken().loc;
      if (!Operand(sequence, kind) || !Require(kind, Kind::kSequence, kAt)) {
        return false;
      }
      kind = Kind::kSequence;
      return true;
    }
    if (p_.Check(TokenKind::kAt)) {
      return ClockingEvent() && Operand(sequence, kind);
    }
    const PrefixForm* form = FindPrefixForm(p_.CurrentToken().kind, sequence);
    return form != nullptr ? Prefixed(*form, kind) : Primary(sequence, kind);
  }

  bool Prefixed(const PrefixForm& form, Kind& kind) {
    p_.Consume();
    kind = form.property ? Kind::kProperty : Kind::kSequence;
    Kind inner = Kind::kBoolean;
    switch (form.opener) {
      case Opener::kOptionalBracket:
        if (!p_.Check(TokenKind::kLBracket)) return PrefixOperand(form);
        return Bracket(form.bounds, form.dollar) && PrefixOperand(form);
      case Opener::kBracket:
        return Bracket(form.bounds, form.dollar) && PrefixOperand(form);
      case Opener::kCondition:
        return Condition() && PrefixOperand(form);
      case Opener::kStrength:
        return Parenthesis({false, false, true}, inner);
      case Opener::kFirstMatch:
        return Parenthesis({false, true, true}, inner);
      case Opener::kIf: {
        Kind branch = Kind::kBoolean;
        return Condition() && Chain(false, branch) &&
               (!p_.Match(TokenKind::kKwElse) || Chain(false, branch));
      }
      case Opener::kCase:
        return Condition() && CaseItem();
      default:
        return PrefixOperand(form);
    }
  }

  bool PrefixOperand(const PrefixForm& form) {
    Kind operand = Kind::kBoolean;
    return Climb(false, form.lowest ? 0 : kNotPrecedence + 1, operand);
  }

  bool Primary(bool sequence, Kind& kind) {
    const SourceLoc kAt = p_.CurrentToken().loc;
    auto saved = p_.lexer_.SavePos();
    if (Read(Reading::kExpressionOrDist) != nullptr && AtOperandEnd()) {
      kind = Kind::kBoolean;
      return Repetition(kind, kAt);
    }
    p_.lexer_.RestorePos(saved);
    if (p_.Check(TokenKind::kLParen)) {
      return Parenthesis({sequence, true, false}, kind) &&
             Repetition(kind, kAt);
    }
    kind = Kind::kInstance;
    return p_.Check(TokenKind::kIdentifier) && Instance() &&
           Repetition(kind, kAt);
  }

  bool AtOperandEnd() {
    const TokenKind kKind = p_.CurrentToken().kind;
    if (IsJoin(kKind, false) || AtRepetition() ||
        std::find(kOperandEnds.begin(), kOperandEnds.end(), kKind) !=
            kOperandEnds.end()) {
      return true;
    }
    return Fail();
  }

  bool Parenthesis(Group group, Kind& kind) {
    if (!p_.Match(TokenKind::kLParen)) return Fail();
    const SourceLoc kAt = p_.CurrentToken().loc;
    if (!Chain(group.sequence, kind)) return false;
    const bool kItems = group.match_items && p_.Check(TokenKind::kComma);
    if ((group.sequence_only || kItems) &&
        !Require(kind, Kind::kSequence, kAt)) {
      return false;
    }
    if (kItems) kind = Kind::kSequence;
    while (group.match_items && p_.Match(TokenKind::kComma)) {
      if (!MatchItem()) return false;
    }
    return Expect(TokenKind::kRParen);
  }

  bool MatchItem() {
    const Expr* item = Read(Reading::kExpression);
    if (item == nullptr) return false;
    const TokenKind kKind = p_.CurrentToken().kind;
    if (kKind == TokenKind::kEq || IsCompoundAssignOp(kKind)) {
      p_.Consume();
      return Expression(Reading::kExpression);
    }
    if (IsMatchItemExpr(*item)) return true;
    return Fail();
  }

  bool Instance() {
    p_.Consume();
    while (p_.Match(TokenKind::kDot) || p_.Match(TokenKind::kColonColon)) {
      if (!p_.Match(TokenKind::kIdentifier)) return Fail();
    }
    if (!p_.Match(TokenKind::kLParen)) return Fail();
    bool named = false;
    do {
      if (!ListArg(named)) return false;
    } while (p_.Match(TokenKind::kComma));
    return Expect(TokenKind::kRParen);
  }

  bool ListArg(bool& named) {
    const bool kEmpty =
        p_.Check(TokenKind::kComma) || p_.Check(TokenKind::kRParen);
    if (p_.Match(TokenKind::kDot)) {
      named = true;
      return NamedArg();
    }
    if (named) return Fail();
    return kEmpty || ActualArg();
  }

  bool ActualArg() {
    if (p_.Match(TokenKind::kDollar)) return true;
    if (std::find(kEdges.begin(), kEdges.end(), p_.CurrentToken().kind) !=
        kEdges.end()) {
      return EdgeEvent();
    }
    Kind kind = Kind::kBoolean;
    return Chain(false, kind);
  }

  bool NamedArg() {
    if (!p_.Match(TokenKind::kIdentifier) || !p_.Match(TokenKind::kLParen)) {
      return Fail();
    }
    if (p_.Check(TokenKind::kRParen)) return Expect(TokenKind::kRParen);
    return ActualArg() && Expect(TokenKind::kRParen);
  }

  bool EdgeEvent() {
    p_.Consume();
    if (!Expression(Reading::kExpression)) return false;
    if (p_.Match(TokenKind::kKwIff) && !Expression(Reading::kExpression)) {
      return false;
    }
    return !p_.Match(TokenKind::kKwOr) || ActualArg();
  }

  bool CaseItem() {
    if (p_.Match(TokenKind::kKwDefault)) {
      p_.Match(TokenKind::kColon);
    } else if (!CaseLabels()) {
      return false;
    }
    Kind kind = Kind::kBoolean;
    if (!Chain(false, kind)) return false;
    if (!p_.Match(TokenKind::kSemicolon)) return Fail();
    return p_.Match(TokenKind::kKwEndcase) || CaseItem();
  }

  bool CaseLabels() {
    do {
      if (!Expression(Reading::kExpressionOrDist)) return false;
    } while (p_.Match(TokenKind::kComma));
    return Expect(TokenKind::kColon);
  }

  bool ClockingEvent() {
    p_.Consume();
    const uint32_t kErrors = p_.diag_.SuppressedErrorCount();
    if (p_.Match(TokenKind::kLParen)) {
      p_.ParseEventList();
      if (!Clean(kErrors)) return false;
      return Expect(TokenKind::kRParen);
    }
    p_.ParseNamedClockingEvent();
    return Clean(kErrors);
  }

  bool CycleDelay() {
    p_.Consume();
    if (!p_.Match(TokenKind::kLBracket)) return Expression(Reading::kPrimary);
    if (p_.Match(TokenKind::kStar) || p_.Match(TokenKind::kPlus)) {
      return Expect(TokenKind::kRBracket);
    }
    return BracketBody(Bounds::kRange, true);
  }

  bool AtRepetition() {
    if (!p_.Check(TokenKind::kLBracket)) return false;
    auto saved = p_.lexer_.SavePos();
    p_.Consume();
    const TokenKind kKind = p_.CurrentToken().kind;
    p_.lexer_.RestorePos(saved);
    return std::find(kRepetitionOpeners.begin(), kRepetitionOpeners.end(),
                     kKind) != kRepetitionOpeners.end();
  }

  bool Repetition(Kind& kind, SourceLoc at) {
    if (!AtRepetition()) return true;
    if (!Require(kind, Kind::kSequence, at)) return false;
    const bool kBoolean = kind == Kind::kBoolean;
    kind = Kind::kSequence;
    p_.Consume();
    if (p_.Match(TokenKind::kPlus)) {
      return Expect(TokenKind::kRBracket);
    }
    if (p_.Match(TokenKind::kStar)) {
      return p_.Match(TokenKind::kRBracket) ||
             BracketBody(Bounds::kEither, true);
    }
    if (!kBoolean) return Fail();
    p_.Consume();
    return BracketBody(Bounds::kEither, true);
  }

  bool Bracket(Bounds bounds, bool dollar) {
    if (!p_.Match(TokenKind::kLBracket)) return Fail();
    return BracketBody(bounds, dollar);
  }

  bool BracketBody(Bounds bounds, bool dollar) {
    if (!Expression(Reading::kExpression)) return false;
    if (bounds != Bounds::kSingle && p_.Match(TokenKind::kColon)) {
      if (!RangeEnd(dollar)) return false;
    } else if (bounds == Bounds::kRange) {
      return Fail();
    }
    return Expect(TokenKind::kRBracket);
  }

  bool RangeEnd(bool dollar) {
    if (!p_.Check(TokenKind::kDollar)) return Expression(Reading::kExpression);
    if (!dollar) return Fail();
    p_.Consume();
    return true;
  }

  Parser& p_;
  bool sequence_;
  bool body_;
  SourceLoc furthest_;
  SourceLoc misplaced_at_;
  const char* misplaced_ = nullptr;
};

bool ParserPropertyGrammar::CheckPropertySpec(Parser& p, bool sequence) {
  return Recognize(p, sequence, false, TokenKind::kRParen);
}

bool ParserPropertyGrammar::CheckDeclarationBody(Parser& p, bool sequence,
                                                 TokenKind end) {
  return Recognize(p, sequence, true, end);
}

bool ParserPropertyGrammar::Recognize(Parser& p, bool sequence, bool body,
                                      TokenKind end) {
  auto saved = p.lexer_.SavePos();
  bool was_in_sequence_body = p.in_sequence_body_;
  p.in_sequence_body_ = true;
  p.diag_.PushSuppress();
  Scan scan(p, sequence, body);
  const bool kAdmitted = body ? scan.Body(end) : scan.Spec();
  p.diag_.PopSuppress();
  p.in_sequence_body_ = was_in_sequence_body;
  p.lexer_.RestorePos(saved);
  if (!kAdmitted) scan.Report();
  return kAdmitted;
}

}  // namespace delta
