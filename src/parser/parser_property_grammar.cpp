#include "parser/parser_property_grammar.h"

#include <algorithm>
#include <array>
#include <cstdint>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"
#include "parser/parser_token_skips.h"

// §A.2.10's property_spec, property_expr and sequence_expr, recognized
// rather than parsed: the spec is read as a chain of operands joined by the
// binary operators of the two productions, each operand with the operators
// and the cycle delays written before it. The precedence and associativity
// of Tables 16-1 and 16-3 decide how an admitted spec groups, never whether
// it is admitted, so the chain is read flat. Where the grammar asks for a
// sequence_expr, the left of an implication or the operand of strong, an
// operand that is only a property_expr is not told apart; the one place the
// difference is read is a cover sequence statement's spec, which no
// property operator may stand in.

namespace delta {

namespace {

// The binary operators of the chain: §16.9's, joining two sequences, and
// the property operators of §16.12, joining two properties.
struct JoinForm {
  TokenKind kind;
  bool property;
};

constexpr std::array<JoinForm, 15> kJoins = {{
    {TokenKind::kKwAnd, false},
    {TokenKind::kKwOr, false},
    {TokenKind::kKwIntersect, false},
    {TokenKind::kKwWithin, false},
    {TokenKind::kKwThroughout, false},
    {TokenKind::kPipeDashGt, true},
    {TokenKind::kPipeEqGt, true},
    {TokenKind::kHashMinusHash, true},
    {TokenKind::kHashEqHash, true},
    {TokenKind::kKwUntil, true},
    {TokenKind::kKwSUntil, true},
    {TokenKind::kKwUntilWith, true},
    {TokenKind::kKwSUntilWith, true},
    {TokenKind::kKwImplies, true},
    {TokenKind::kKwIff, true},
}};

// Whether `kind` joins two operands of a chain read as a sequence_expr where
// `sequence` is set and as a property_expr otherwise.
bool IsJoin(TokenKind kind, bool sequence) {
  return std::any_of(kJoins.begin(), kJoins.end(),
                     [kind, sequence](const JoinForm& join) {
                       return join.kind == kind && !(sequence && join.property);
                     });
}

// What stands in a bracket: one constant_expression, a range `lo : hi`, or
// either.
enum class Bounds : uint8_t { kSingle, kRange, kEither };

// What an operator written before its operand reads before the operand, or
// in its place.
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

// An operator written before its operand: the bracket it takes, with the
// bounds the bracket holds and whether a range in it may end in `$`, and
// whether only a property_expr has the operator.
struct PrefixForm {
  TokenKind kind;
  Opener opener;
  Bounds bounds;
  bool dollar;
  bool property;
};

// §16.12.2, §16.12.3, §16.12.6, §16.12.10, §16.12.11, §16.12.13,
// §16.12.14 and §16.12.16: not, nexttime with a
// constant_expression, always and s_eventually with a
// cycle_delay_const_range_expression, s_always and eventually with a
// constant_range, the aborts with their condition, strong and weak, if and
// case; and §16.9.8's first_match, which a sequence_expr has as well.
constexpr std::array<PrefixForm, 16> kPrefixForms = {{
    {TokenKind::kKwNot, Opener::kNone, Bounds::kSingle, false, true},
    {TokenKind::kKwNexttime, Opener::kOptionalBracket, Bounds::kSingle, false,
     true},
    {TokenKind::kKwSNexttime, Opener::kOptionalBracket, Bounds::kSingle, false,
     true},
    {TokenKind::kKwAlways, Opener::kOptionalBracket, Bounds::kRange, true,
     true},
    {TokenKind::kKwSEventually, Opener::kOptionalBracket, Bounds::kRange, true,
     true},
    {TokenKind::kKwSAlways, Opener::kBracket, Bounds::kRange, false, true},
    {TokenKind::kKwEventually, Opener::kBracket, Bounds::kRange, false, true},
    {TokenKind::kKwAcceptOn, Opener::kCondition, Bounds::kSingle, false, true},
    {TokenKind::kKwRejectOn, Opener::kCondition, Bounds::kSingle, false, true},
    {TokenKind::kKwSyncAcceptOn, Opener::kCondition, Bounds::kSingle, false,
     true},
    {TokenKind::kKwSyncRejectOn, Opener::kCondition, Bounds::kSingle, false,
     true},
    {TokenKind::kKwStrong, Opener::kStrength, Bounds::kSingle, false, true},
    {TokenKind::kKwWeak, Opener::kStrength, Bounds::kSingle, false, true},
    {TokenKind::kKwFirstMatch, Opener::kFirstMatch, Bounds::kSingle, false,
     false},
    {TokenKind::kKwIf, Opener::kIf, Bounds::kSingle, false, true},
    {TokenKind::kKwCase, Opener::kCase, Bounds::kSingle, false, true},
}};

// The operator `kind` is, written before an operand of a chain read as a
// sequence_expr where `sequence` is set; null where it is none.
const PrefixForm* FindPrefixForm(TokenKind kind, bool sequence) {
  auto found =
      std::find_if(kPrefixForms.begin(), kPrefixForms.end(),
                   [kind, sequence](const PrefixForm& form) {
                     return form.kind == kind && !(sequence && form.property);
                   });
  return found == kPrefixForms.end() ? nullptr : &*found;
}

// The tokens an operand read as an expression may stand before, besides a
// binary operator of the chain and a repetition: a group's or the spec's
// closing parenthesis, the comma before a match item or the next actual
// argument, the semicolon ending a case item, a cycle delay, and the else
// of an if.
constexpr std::array<TokenKind, 5> kOperandEnds = {
    TokenKind::kRParen, TokenKind::kComma, TokenKind::kSemicolon,
    TokenKind::kHashHash, TokenKind::kKwElse};

// The token after the `[` of §16.9.2's repetitions: `[*`, `[->`, `[=` and
// `[+]`.
constexpr std::array<TokenKind, 4> kRepetitionOpeners = {
    TokenKind::kStar, TokenKind::kArrow, TokenKind::kEq, TokenKind::kPlus};

// §9.4.2's edges, which open an event_expression an instance's actual
// argument may be (§16.8).
constexpr std::array<TokenKind, 3> kEdges = {
    TokenKind::kKwPosedge, TokenKind::kKwNegedge, TokenKind::kKwEdge};

// §16.10 and §16.11: whether an expression read as a sequence_match_item
// other than an operator_assignment is one, a subroutine call or an
// inc_or_dec_expression.
bool IsMatchItemExpr(const Expr& expr) {
  if (expr.kind == ExprKind::kCall || expr.kind == ExprKind::kSystemCall ||
      expr.kind == ExprKind::kPostfixUnary) {
    return true;
  }
  return expr.kind == ExprKind::kUnary &&
         (expr.op == TokenKind::kPlusPlus || expr.op == TokenKind::kMinusMinus);
}

// Where a token stands, in an order a later token is greater in.
uint64_t Order(SourceLoc loc) {
  return (uint64_t{loc.line} << 32) | loc.column;
}

// What an operand's expression is read as: an expression, an
// expression_or_dist, or the constant_primary of a cycle delay.
enum class Reading : uint8_t { kExpression, kExpressionOrDist, kPrimary };

}  // namespace

// One recognition of a spec: the parser it reads from, whether the spec is
// a cover sequence statement's, and the furthest point a reading of it
// failed at.
class ParserPropertyGrammar::Scan {
 public:
  Scan(Parser& p, bool sequence) : p_(p), sequence_(sequence) {}

  // property_spec, or the cover sequence statement's spec, up to the
  // parenthesis closing it.
  bool Spec() {
    if (p_.Check(TokenKind::kAt) && !ClockingEvent()) return false;
    if (p_.Match(TokenKind::kKwDisable) && !DisableIff()) return false;
    return Chain(sequence_) && (p_.Check(TokenKind::kRParen) || Fail());
  }

  void Report() const {
    p_.diag_.Error(furthest_,
                   "this concurrent assertion's spec is not one the grammar "
                   "admits: no reading of it gets past this point",
                   Subclause("A.2.10"));
  }

 private:
  // Notes `loc` as a point a reading failed at, where it is further than any
  // before; answers false, the reading's answer.
  bool FailAt(SourceLoc loc) {
    if (Order(loc) > Order(furthest_)) furthest_ = loc;
    return false;
  }

  bool Fail() { return FailAt(p_.CurrentToken().loc); }

  // Whether nothing read since the suppressed errors numbered `errors` was
  // reported, noting where the last report stood where something was: a
  // reading reports where it broke off, and may have gone past it.
  bool Clean(uint32_t errors) {
    return p_.diag_.SuppressedErrorCount() == errors ||
           FailAt(p_.diag_.LastSuppressedErrorLoc());
  }

  // The expression `reading` reads from the current token, or null where it
  // reads none without an error.
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

  // `disable iff ( expression_or_dist )`, its `disable` read.
  bool DisableIff() {
    return (p_.Match(TokenKind::kKwIff) || Fail()) && Condition();
  }

  // `( expression_or_dist )`, the condition of an if, a case, an abort and
  // a disable.
  bool Condition() {
    if (!p_.Match(TokenKind::kLParen)) return Fail();
    return Expression(Reading::kExpressionOrDist) &&
           (p_.Match(TokenKind::kRParen) || Fail());
  }

  // An operand and every operand the chain's binary operators and cycle
  // delays join to it.
  bool Chain(bool sequence) {
    while (Operand(sequence)) {
      if (p_.Check(TokenKind::kHashHash)) continue;
      if (!IsJoin(p_.CurrentToken().kind, sequence)) return true;
      p_.Consume();
    }
    return false;
  }

  // One operand with the cycle delays, the clocking events and the
  // operators written before it.
  bool Operand(bool sequence) {
    while (p_.Check(TokenKind::kHashHash)) {
      if (!CycleDelay()) return false;
    }
    if (p_.Check(TokenKind::kAt)) return ClockingEvent() && Operand(sequence);
    const PrefixForm* form = FindPrefixForm(p_.CurrentToken().kind, sequence);
    return form != nullptr ? Prefixed(*form) : Primary(sequence);
  }

  // The operand of an operator written before it, or what the operator
  // stands for whole, the operator read from the current token.
  bool Prefixed(const PrefixForm& form) {
    p_.Consume();
    switch (form.opener) {
      case Opener::kOptionalBracket:
        if (!p_.Check(TokenKind::kLBracket)) return Operand(false);
        return Bracket(form.bounds, form.dollar) && Operand(false);
      case Opener::kBracket:
        return Bracket(form.bounds, form.dollar) && Operand(false);
      case Opener::kCondition:
        return Condition() && Operand(false);
      case Opener::kStrength:
        return Parenthesis(true, false);
      case Opener::kFirstMatch:
        return Parenthesis(true, true);
      case Opener::kIf:
        return Condition() && Chain(false) &&
               (!p_.Match(TokenKind::kKwElse) || Chain(false));
      case Opener::kCase:
        return Condition() && CaseItem();
      default:
        return Operand(false);
    }
  }

  // An operand no operator stands before: an expression_or_dist, a
  // parenthesized sequence_expr or property_expr where no expression reads
  // to a token an operand ends at, `(a) + b` being an expression, or an
  // instance whose actual arguments no expression reads; with the
  // repetition after it.
  bool Primary(bool sequence) {
    auto saved = p_.lexer_.SavePos();
    if (Read(Reading::kExpressionOrDist) != nullptr && AtOperandEnd()) {
      return Repetition(true);
    }
    p_.lexer_.RestorePos(saved);
    if (p_.Check(TokenKind::kLParen)) {
      return Parenthesis(sequence, true) && Repetition(false);
    }
    return p_.Check(TokenKind::kIdentifier) && Instance() && Repetition(false);
  }

  bool AtOperandEnd() {
    const TokenKind kKind = p_.CurrentToken().kind;
    return IsJoin(kKind, false) || AtRepetition() ||
           std::find(kOperandEnds.begin(), kOperandEnds.end(), kKind) !=
               kOperandEnds.end() ||
           Fail();
  }

  // `( chain )`, with the sequence_match_items after the chain where
  // `match_items` is set (§16.10).
  bool Parenthesis(bool sequence, bool match_items) {
    if (!p_.Match(TokenKind::kLParen)) return Fail();
    if (!Chain(sequence)) return false;
    while (match_items && p_.Match(TokenKind::kComma)) {
      if (!MatchItem()) return false;
    }
    return p_.Match(TokenKind::kRParen) || Fail();
  }

  // §16.10 and §16.11: an operator_assignment, an inc_or_dec_expression or
  // a subroutine call.
  bool MatchItem() {
    const Expr* item = Read(Reading::kExpression);
    if (item == nullptr) return false;
    const TokenKind kKind = p_.CurrentToken().kind;
    if (kKind == TokenKind::kEq || IsCompoundAssignOp(kKind)) {
      p_.Consume();
      return Expression(Reading::kExpression);
    }
    return IsMatchItemExpr(*item) || Fail();
  }

  // §16.8 and §16.12: a sequence_instance or a property_instance, a name,
  // `.` or `::` qualified, and its parenthesized actual arguments.
  bool Instance() {
    p_.Consume();
    while (p_.Match(TokenKind::kDot) || p_.Match(TokenKind::kColonColon)) {
      if (!p_.Match(TokenKind::kIdentifier)) return Fail();
    }
    if (!p_.Match(TokenKind::kLParen)) return Fail();
    do {
      if (!ActualArg()) return false;
    } while (p_.Match(TokenKind::kComma));
    return p_.Match(TokenKind::kRParen) || Fail();
  }

  // One actual argument: none, `.name ( [actual] )`, `$`, an
  // event_expression opening with an edge, or a property_expr, which a
  // sequence_expr and the other event_expressions are.
  bool ActualArg() {
    if (p_.Check(TokenKind::kComma) || p_.Check(TokenKind::kRParen)) {
      return true;
    }
    if (p_.Match(TokenKind::kDot)) return NamedArg();
    if (p_.Match(TokenKind::kDollar)) return true;
    if (std::find(kEdges.begin(), kEdges.end(), p_.CurrentToken().kind) !=
        kEdges.end()) {
      return EdgeEvent();
    }
    return Chain(false);
  }

  // `name ( [actual] )`, its `.` read.
  bool NamedArg() {
    if (!p_.Match(TokenKind::kIdentifier) || !p_.Match(TokenKind::kLParen)) {
      return Fail();
    }
    return ActualArg() && (p_.Match(TokenKind::kRParen) || Fail());
  }

  // §9.4.2: `edge expression [iff expression]`, and the event_expressions
  // `or` joins to it.
  bool EdgeEvent() {
    p_.Consume();
    if (!Expression(Reading::kExpression)) return false;
    if (p_.Match(TokenKind::kKwIff) && !Expression(Reading::kExpression)) {
      return false;
    }
    return !p_.Match(TokenKind::kKwOr) || ActualArg();
  }

  // §16.12.16: the property_case_items of a case after its condition, up to
  // and with its endcase.
  bool CaseItem() {
    if (p_.Match(TokenKind::kKwDefault)) {
      p_.Match(TokenKind::kColon);
    } else if (!CaseLabels()) {
      return false;
    }
    if (!Chain(false)) return false;
    if (!p_.Match(TokenKind::kSemicolon)) return Fail();
    return p_.Match(TokenKind::kKwEndcase) || CaseItem();
  }

  // A case item's expression_or_dists and the colon after them.
  bool CaseLabels() {
    do {
      if (!Expression(Reading::kExpressionOrDist)) return false;
    } while (p_.Match(TokenKind::kComma));
    return p_.Match(TokenKind::kColon) || Fail();
  }

  // §9.4.2 and §16.5: `@ identifier` or `@ ( event_expression )`.
  bool ClockingEvent() {
    p_.Consume();
    const uint32_t kErrors = p_.diag_.SuppressedErrorCount();
    if (p_.Match(TokenKind::kLParen)) {
      p_.ParseEventList();
      if (!Clean(kErrors)) return false;
      return p_.Match(TokenKind::kRParen) || Fail();
    }
    p_.ParseNamedClockingEvent();
    return Clean(kErrors);
  }

  // §16.7: a cycle_delay_range, `## constant_primary`, `## [ range ]`,
  // `##[*]` or `##[+]`.
  bool CycleDelay() {
    p_.Consume();
    if (!p_.Match(TokenKind::kLBracket)) return Expression(Reading::kPrimary);
    if (p_.Match(TokenKind::kStar) || p_.Match(TokenKind::kPlus)) {
      return p_.Match(TokenKind::kRBracket) || Fail();
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

  // §16.9.2: the repetition after an operand, if any: consecutive on any
  // operand, and goto and nonconsecutive on a `boolean` one alone.
  bool Repetition(bool boolean) {
    if (!AtRepetition()) return true;
    p_.Consume();
    if (p_.Match(TokenKind::kPlus)) {
      return p_.Match(TokenKind::kRBracket) || Fail();
    }
    if (p_.Match(TokenKind::kStar)) {
      return p_.Match(TokenKind::kRBracket) ||
             BracketBody(Bounds::kEither, true);
    }
    if (!boolean) return Fail();
    p_.Consume();
    return BracketBody(Bounds::kEither, true);
  }

  bool Bracket(Bounds bounds, bool dollar) {
    if (!p_.Match(TokenKind::kLBracket)) return Fail();
    return BracketBody(bounds, dollar);
  }

  // What a bracket holds as `bounds` has it, a range's `hi` being `$` where
  // `dollar` is set, and the `]` closing it, its `[` read.
  bool BracketBody(Bounds bounds, bool dollar) {
    if (!Expression(Reading::kExpression)) return false;
    if (bounds != Bounds::kSingle && p_.Match(TokenKind::kColon)) {
      if (!RangeEnd(dollar)) return false;
    } else if (bounds == Bounds::kRange) {
      return Fail();
    }
    return p_.Match(TokenKind::kRBracket) || Fail();
  }

  bool RangeEnd(bool dollar) {
    if (!p_.Check(TokenKind::kDollar)) return Expression(Reading::kExpression);
    if (!dollar) return Fail();
    p_.Consume();
    return true;
  }

  Parser& p_;
  bool sequence_;
  SourceLoc furthest_;
};

bool ParserPropertyGrammar::CheckPropertySpec(Parser& p, bool sequence) {
  auto saved = p.lexer_.SavePos();
  bool was_in_sequence_body = p.in_sequence_body_;
  p.in_sequence_body_ = true;
  p.diag_.PushSuppress();
  Scan scan(p, sequence);
  const bool kAdmitted = scan.Spec();
  p.diag_.PopSuppress();
  p.in_sequence_body_ = was_in_sequence_body;
  p.lexer_.RestorePos(saved);
  if (!kAdmitted) scan.Report();
  return kAdmitted;
}

}  // namespace delta
