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

// §A.2.10's property_spec, property_expr and sequence_expr, recognized
// rather than parsed: the spec is read as a chain of operands joined by the
// binary operators of the two productions, each operand with the operators
// and the cycle delays written before it, grouped by the precedence and
// associativity of Table 16-3, which places §16.9's sequence operators above
// §16.12's property operators. Each operand reports what it is: an
// expression_or_dist, a sequence_expr, or a property_expr, which only a
// property operator makes; an instance of a named sequence or property is
// either, since its declaration is not read here. Where the grammar asks for
// a sequence_expr -- an operand of a sequence operator, the left of an
// implication, the operand of strong, weak and first_match, a repeated
// operand and one with match items -- a property_expr is reported, as a
// sequence_expr is on the left of throughout, which takes an
// expression_or_dist. A cover sequence statement's spec reads no property
// operator at all.

namespace delta {

namespace {

// What an operand or a chain of them is: an expression_or_dist, a
// sequence_expr, an instance, which may be any of them, or a property_expr.
// Each is admitted where the grammar admits an earlier one, an instance
// aside, and an `and` or an `or` makes the latest of its operands' kinds.
enum class Kind : uint8_t { kBoolean, kSequence, kInstance, kProperty };

// Whether `kind` stands where the grammar admits `most`, an
// expression_or_dist or a sequence_expr, and what is below it.
bool Fits(Kind kind, Kind most) {
  return kind == Kind::kInstance || kind <= most;
}

// What a binary operator takes and makes: two sequence_exprs and a
// sequence_expr; an expression_or_dist and a sequence_expr, throughout's
// (§16.9.9); either, `and` and `or`; a sequence_expr and a property_expr, an
// implication's or a followed-by's (§16.12.7, §16.12.9); or two
// property_exprs.
enum class Operands : uint8_t {
  kSequences,
  kBooleanSequence,
  kEither,
  kSequenceProperty,
  kProperties,
};

// The binary operators of the chain, each with its Table 16-3 row, a higher
// one binding tighter, whether it groups to the right, and its operands.
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

// Table 16-3's row of not, nexttime and s_nexttime, between intersect's and
// and's; the rows below and's are the property operators.
constexpr int kNotPrecedence = 5;

// The binary operator `kind` is, joining two operands of a chain read as a
// sequence_expr where `sequence` is set and as a property_expr otherwise;
// null where it is none.
const JoinForm* FindJoin(TokenKind kind, bool sequence) {
  auto found = std::find_if(
      kJoins.begin(), kJoins.end(), [kind, sequence](const JoinForm& join) {
        return join.kind == kind &&
               !(sequence && join.precedence < kNotPrecedence);
      });
  return found == kJoins.end() ? nullptr : &*found;
}

bool IsJoin(TokenKind kind, bool sequence) {
  return FindJoin(kind, sequence) != nullptr;
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
// bounds the bracket holds and whether a range in it may end in `$`, whether
// only a property_expr has the operator, and whether its operand runs to the
// end of the chain, as Table 16-3's last row has it, where not, nexttime and
// s_nexttime take only what their row binds tighter.
struct PrefixForm {
  TokenKind kind;
  Opener opener;
  Bounds bounds;
  bool dollar;
  bool property;
  bool lowest;
};

// §16.12.2, §16.12.3, §16.12.6, §16.12.10, §16.12.11, §16.12.13,
// §16.12.14 and §16.12.16: not, nexttime with a
// constant_expression, always and s_eventually with a
// cycle_delay_const_range_expression, s_always and eventually with a
// constant_range, the aborts with their condition, strong and weak, if and
// case; and §16.9.8's first_match, which a sequence_expr has as well.
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

// A parenthesized chain: whether it is read as a sequence_expr, whether
// sequence_match_items may follow it (§16.10), and whether the grammar admits
// only a sequence_expr in it, as strong, weak and first_match do.
struct Group {
  bool sequence;
  bool match_items;
  bool sequence_only;
};

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
    Kind kind = Kind::kBoolean;
    if (!Chain(sequence_, kind)) return false;
    if (p_.Check(TokenKind::kRParen)) return true;
    return Fail();
  }

  void Report() const {
    if (misplaced_ != nullptr) {
      p_.diag_.Error(misplaced_at_, misplaced_, Subclause("A.2.10"));
      return;
    }
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

  // Whether an operand of `kind` that starts at `at` stands where the grammar
  // admits `most`; where it does not, notes why, which is the report made.
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

  // Reads the current token where it is `kind`; notes a failure where it is
  // not.
  bool Expect(TokenKind kind) {
    if (p_.Match(kind)) return true;
    return Fail();
  }

  // Whether nothing read since the suppressed errors numbered `errors` was
  // reported, noting where the last report stood where something was: a
  // reading reports where it broke off, and may have gone past it.
  bool Clean(uint32_t errors) {
    if (p_.diag_.SuppressedErrorCount() == errors) return true;
    return FailAt(p_.diag_.LastSuppressedErrorLoc());
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
  bool DisableIff() { return Expect(TokenKind::kKwIff) && Condition(); }

  // `( expression_or_dist )`, the condition of an if, a case, an abort and
  // a disable.
  bool Condition() {
    if (!p_.Match(TokenKind::kLParen)) return Fail();
    return Expression(Reading::kExpressionOrDist) && Expect(TokenKind::kRParen);
  }

  // An operand and every operand the chain's binary operators and cycle
  // delays join to it, what they make kept in `kind`.
  bool Chain(bool sequence, Kind& kind) { return Climb(sequence, 0, kind); }

  // An operand and every operand an operator of Table 16-3's row `lowest` or
  // a higher one joins to it, grouped as the rows have them.
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

  // The binary operator `join`, from the current token: the token alone, or
  // a cycle delay with its range.
  bool Operator(const JoinForm& join) {
    if (join.kind == TokenKind::kHashHash) return CycleDelay();
    p_.Consume();
    return true;
  }

  // Whether `join` takes `left`, which starts at `at`, as its left operand;
  // asked before the right one is read, so a break in it is not reported
  // first.
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

  // Whether `join` takes `right`, which starts at `at`, as its right
  // operand, what it makes of the two kept in `left`.
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

  // One operand with the cycle delays, the clocking events and the
  // operators written before it, what it is kept in `kind`.
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

  // The operand of an operator written before it, or what the operator
  // stands for whole, the operator read from the current token; what it
  // makes kept in `kind`.
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

  // The property_expr an operator written before it takes: the rest of the
  // chain for an operator of Table 16-3's last row, and for not, nexttime
  // and s_nexttime what the rows above theirs join.
  bool PrefixOperand(const PrefixForm& form) {
    Kind operand = Kind::kBoolean;
    return Climb(false, form.lowest ? 0 : kNotPrecedence + 1, operand);
  }

  // An operand no operator stands before: an expression_or_dist, a
  // parenthesized sequence_expr or property_expr where no expression reads
  // to a token an operand ends at, `(a) + b` being an expression, or an
  // instance whose actual arguments no expression reads; with the
  // repetition after it.
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

  // `( chain )`, with the sequence_match_items after the chain where the
  // group takes them (§16.10), what it holds kept in `kind`. A chain that
  // match items follow, or that the group admits only as a sequence_expr,
  // is one.
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
    if (IsMatchItemExpr(*item)) return true;
    return Fail();
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
    return Expect(TokenKind::kRParen);
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
    Kind kind = Kind::kBoolean;
    return Chain(false, kind);
  }

  // `name ( [actual] )`, its `.` read.
  bool NamedArg() {
    if (!p_.Match(TokenKind::kIdentifier) || !p_.Match(TokenKind::kLParen)) {
      return Fail();
    }
    return ActualArg() && Expect(TokenKind::kRParen);
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
    Kind kind = Kind::kBoolean;
    if (!Chain(false, kind)) return false;
    if (!p_.Match(TokenKind::kSemicolon)) return Fail();
    return p_.Match(TokenKind::kKwEndcase) || CaseItem();
  }

  // A case item's expression_or_dists and the colon after them.
  bool CaseLabels() {
    do {
      if (!Expression(Reading::kExpressionOrDist)) return false;
    } while (p_.Match(TokenKind::kComma));
    return Expect(TokenKind::kColon);
  }

  // §9.4.2 and §16.5: `@ identifier` or `@ ( event_expression )`.
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

  // §16.7: a cycle_delay_range, `## constant_primary`, `## [ range ]`,
  // `##[*]` or `##[+]`.
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

  // §16.9.2: the repetition after an operand of `kind` that starts at `at`,
  // if any: consecutive on a sequence_expr, and goto and nonconsecutive on
  // an expression_or_dist alone; what it makes, a sequence_expr, kept in
  // `kind`.
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

  // What a bracket holds as `bounds` has it, a range's `hi` being `$` where
  // `dollar` is set, and the `]` closing it, its `[` read.
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
  SourceLoc furthest_;
  // Where an operand stands that the grammar does not admit there, and the
  // report made of it, which a misreading of the spec does not override.
  SourceLoc misplaced_at_;
  const char* misplaced_ = nullptr;
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
