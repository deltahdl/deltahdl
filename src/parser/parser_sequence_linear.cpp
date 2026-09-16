#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"
#include "parser/parser_sequence_property_decl_internal.h"

namespace delta {

// §16.13.6/§9.4.4: the trial parse that captures a sequence body's linear form
// for the simulator's sequence monitor, held apart from the Parser's own
// methods as the other helper structs are, so the declarations the parser
// header carries stay within the gate on its length.
struct ParserSeqLinearHelpers {
  // Whether the token is one of §11.4.1's assignment operators other than `=`.
  static bool IsCompoundAssignToken(TokenKind kind) {
    switch (kind) {
      case TokenKind::kPlusEq:
      case TokenKind::kMinusEq:
      case TokenKind::kStarEq:
      case TokenKind::kSlashEq:
      case TokenKind::kPercentEq:
      case TokenKind::kAmpEq:
      case TokenKind::kPipeEq:
      case TokenKind::kCaretEq:
      case TokenKind::kLtLtEq:
      case TokenKind::kGtGtEq:
      case TokenKind::kLtLtLtEq:
      case TokenKind::kGtGtGtEq:
        return true;
      default:
        return false;
    }
  }

  // §16.7: a delay owed before a group and the delay the group's chain opens
  // with add, unbounded where either is.
  static SeqCycleDelay AddSeqDelays(const SeqCycleDelay& a,
                                    const SeqCycleDelay& b) {
    SeqCycleDelay sum;
    sum.min = a.min + b.min;
    bool unbounded = a.max == SeqCycleDelay::kUnbounded ||
                     b.max == SeqCycleDelay::kUnbounded;
    sum.max = unbounded ? SeqCycleDelay::kUnbounded : a.max + b.max;
    return sum;
  }

  // One bound of §16.7's cycle_delay_range as the linear monitor reads it: an
  // integer literal, `$` where the caller admits it, or the name of a formal
  // argument the instantiation supplies (§16.8). Returns false for any other
  // form, which leaves the sequence without a monitor as before.
  static bool ParseSeqDelayBound(Parser& p, uint32_t& val,
                                 std::string_view& formal, bool dollar) {
    if (p.Check(TokenKind::kIntLiteral)) {
      val = ParseSeqDelayLiteral(p);
      return true;
    }
    if (dollar && p.Match(TokenKind::kDollar)) {
      val = SeqCycleDelay::kUnbounded;
      return true;
    }
    if (p.Check(TokenKind::kIdentifier)) {
      formal = p.Consume().text;
      return true;
    }
    return false;
  }

  // §16.7's cycle_delay_range after its `##`: a constant_primary N for [N:N], a
  // bracketed `a:b` or `a:$`, and the two abbreviations `[*]` for [0:$] and
  // `[+]` for [1:$]. Returns false where the delay is not one of these.
  static bool ParseLinearSeqCycleDelay(Parser& p, SeqCycleDelay& delay) {
    delay = SeqCycleDelay{};
    if (!p.Check(TokenKind::kLBracket)) {
      if (!ParseSeqDelayBound(p, delay.min, delay.min_formal, false)) {
        return false;
      }
      delay.max = delay.min;
      delay.max_formal = delay.min_formal;
      return true;
    }
    p.Consume();  // '['
    if (p.Match(TokenKind::kStar)) {
      delay.min = 0;
      delay.max = SeqCycleDelay::kUnbounded;
      return p.Match(TokenKind::kRBracket);
    }
    if (p.Match(TokenKind::kPlus)) {
      delay.min = 1;
      delay.max = SeqCycleDelay::kUnbounded;
      return p.Match(TokenKind::kRBracket);
    }
    if (!ParseSeqDelayBound(p, delay.min, delay.min_formal, false)) {
      return false;
    }
    if (!p.Match(TokenKind::kColon)) return false;
    if (!ParseSeqDelayBound(p, delay.max, delay.max_formal, true)) {
      return false;
    }
    bool ordered = !delay.min_formal.empty() || !delay.max_formal.empty() ||
                   delay.max >= delay.min;
    return ordered && p.Match(TokenKind::kRBracket);
  }

  static uint32_t ParseSeqDelayLiteral(Parser& p) {
    Token tok = p.Consume();
    uint32_t value = 0;
    for (char c : tok.text) {
      if (c == '_') continue;
      if (c < '0' || c > '9') break;
      value = value * 10 + static_cast<uint32_t>(c - '0');
    }
    return value;
  }

  // Whether the tokens ahead are `identifier ( ... )` followed by what ends an
  // operand -- `##`, `;`, `,`, `)` or `endsequence` -- which is how a sequence
  // instance with an argument list stands in a linear body. The lexer is
  // rewound.
  static bool AheadIsSequenceInstanceOperand(Parser& p) {
    if (!p.Check(TokenKind::kIdentifier)) return false;
    auto saved = p.lexer_.SavePos();
    p.Consume();
    bool is_instance = false;
    if (p.Match(TokenKind::kLParen)) {
      SkipToMatchingParen(p);
      is_instance = p.Check(TokenKind::kHashHash) ||
                    p.Check(TokenKind::kSemicolon) ||
                    p.Check(TokenKind::kComma) || p.Check(TokenKind::kRParen) ||
                    p.Check(TokenKind::kKwEndsequence);
    }
    p.lexer_.RestorePos(saved);
    return is_instance;
  }

  // Consumes the tokens through the `)` matching an `(` already consumed.
  static void SkipToMatchingParen(Parser& p) {
    int depth = 1;
    while (depth > 0 && !p.AtEnd()) {
      if (p.Check(TokenKind::kLParen)) ++depth;
      if (p.Check(TokenKind::kRParen)) --depth;
      p.Consume();
    }
  }

  // Whether the token opens §16.9.2's repetition, `[*`, `[->`, `[=` or `[+]`.
  static bool AtRepetitionBracket(Parser& p) {
    if (!p.Check(TokenKind::kLBracket)) return false;
    auto saved = p.lexer_.SavePos();
    p.Consume();
    bool repetition = p.Check(TokenKind::kStar) || p.Check(TokenKind::kArrow) ||
                      p.Check(TokenKind::kEq) || p.Check(TokenKind::kPlus);
    p.lexer_.RestorePos(saved);
    return repetition;
  }

  // Whether the tokens ahead are a parenthesised group holding a `##`, a `,`,
  // a `throughout` or a repetition at its own depth: a sub-sequence, §16.10's
  // `( sequence_expr , sequence_match_item ... )`, §16.9.9's condition over
  // one or a repeated operand in parentheses, none of which ParseExpr can
  // read. The lexer is rewound.
  static bool AheadIsSequenceGroup(Parser& p) {
    if (!p.Check(TokenKind::kLParen)) return false;
    auto saved = p.lexer_.SavePos();
    p.Consume();
    int depth = 1;
    bool is_group = false;
    while (depth > 0 && !p.AtEnd()) {
      if (p.Check(TokenKind::kLParen)) ++depth;
      if (p.Check(TokenKind::kRParen)) --depth;
      if (depth == 1 &&
          (p.Check(TokenKind::kHashHash) || p.Check(TokenKind::kComma) ||
           p.Check(TokenKind::kKwThroughout) || AtRepetitionBracket(p))) {
        is_group = true;
      }
      p.Consume();
    }
    p.lexer_.RestorePos(saved);
    return is_group;
  }

  // §16.8: a sequence instance's argument list, `sequence_list_of_arguments`,
  // read as a call: each actual is an expression, `$`, kept as an identifier
  // named `$`, or `.formal(actual)` bound by name. The instance is recorded as
  // a call the lowering resolves against the named sequences, so an instance of
  // a sequence declared after this one is reached as §16.8 allows.
  static Expr* ParseSequenceInstanceOperand(Parser& p) {
    Token name = p.Consume();
    auto* call = p.arena_.Create<Expr>();
    call->kind = ExprKind::kCall;
    call->callee = name.text;
    call->text = name.text;
    call->range.start = name.loc;
    p.Expect(TokenKind::kLParen, Subclause("16.8"));
    while (!p.Check(TokenKind::kRParen) && !p.AtEnd()) {
      if (p.Check(TokenKind::kDot)) {
        p.Consume();
        call->arg_names.push_back(
            p.Expect(TokenKind::kIdentifier, Subclause("16.8")).text);
        p.Expect(TokenKind::kLParen, Subclause("16.8"));
        call->args.push_back(ParseSequenceActualArg(p));
        p.Expect(TokenKind::kRParen, Subclause("16.8"));
      } else {
        call->args.push_back(ParseSequenceActualArg(p));
      }
      if (!p.Match(TokenKind::kComma)) break;
    }
    p.Expect(TokenKind::kRParen, Subclause("16.8"));
    return call;
  }

  // §16.8.1: an actual of a sequence instance is read as a property
  // instance's is. One for a formal of type event is an event_expression, so
  // one opening with an edge keyword is kept as the edge over its signal, a
  // unary expression whose operator is the keyword, for the flattening to read
  // as the instantiated sequence's clock; an actual with no edge is an ordinary
  // expression, which an `@(posedge sig)` over a formal sig takes as the
  // signal. §16.13.6: one that is a sequence_expr, for a formal of type
  // sequence, `e2_with_arg(@(posedge sysclk) $rose(a) ##1 b ##1 c)`, is
  // carried by an identifier standing in the argument's place.
  static Expr* ParseSequenceActualArg(Parser& p) {
    bool plain = true;
    return ParserPropertySpecHelpers::ParsePropertyActualArg(p, plain);
  }

  // §16.10 Syntax 16-13: the assertion_variable_declarations a sequence body
  // opens with, each `type name [= init] {, name [= init]} ;` over a data type
  // keyword, recorded as the body's local variables. A declaration in any other
  // shape ends the capture.
  static bool ParseLinearSeqLocalDecls(Parser& p, SeqLinearBody& body) {
    while (IsBuiltinTypeKwForLocalVar(p.CurrentToken().kind)) {
      TokenKind type_kw = p.Consume().kind;
      if (p.Check(TokenKind::kLBracket)) return false;
      do {
        if (!p.Check(TokenKind::kIdentifier)) return false;
        SeqLocalDecl local;
        local.name = p.Consume().text;
        local.type_kw = type_kw;
        if (p.Match(TokenKind::kEq)) local.init = p.ParseExpr();
        body.locals.push_back(local);
      } while (p.Match(TokenKind::kComma));
      if (!p.Match(TokenKind::kSemicolon)) return false;
    }
    return true;
  }

  // The literal 1: §16.9.10's abbreviation stands it where an operand does,
  // and an inc_or_dec_expression adds or subtracts it.
  static Expr* OneLiteral(Parser& p) {
    auto* one = p.arena_.Create<Expr>();
    one->kind = ExprKind::kIntegerLiteral;
    one->text = "1";
    one->int_val = 1;
    one->range.start = p.CurrentToken().loc;
    return one;
  }

  // §16.10: an inc_or_dec_expression as a match item, `lvar++`, `lvar--`,
  // `++lvar` or `--lvar`, is the local updated by one, `lvar += 1` or `lvar
  // -= 1`; `prefix` says the operator stood before the name.
  static bool ParseIncDecMatchItem(Parser& p, SeqMatchAssign& item,
                                   bool prefix) {
    TokenKind op = p.Consume().kind;
    if (prefix) {
      if (!p.Check(TokenKind::kIdentifier)) return false;
      item.lvar = p.Consume().text;
    }
    item.op =
        op == TokenKind::kPlusPlus ? TokenKind::kPlusEq : TokenKind::kMinusEq;
    item.rhs = OneLiteral(p);
    return true;
  }

  // §16.11: whether the tokens ahead are a subroutine call, a system task's
  // name or an identifier followed by `(`, rather than the local an
  // assignment begins with. The lexer is rewound.
  static bool AheadIsSubroutineCall(Parser& p) {
    if (p.Check(TokenKind::kSystemIdentifier)) return true;
    if (!p.Check(TokenKind::kIdentifier)) return false;
    auto saved = p.lexer_.SavePos();
    p.Consume();
    bool call = p.Check(TokenKind::kLParen);
    p.lexer_.RestorePos(saved);
    return call;
  }

  // One match item: §16.11's subroutine call, an inc_or_dec_expression in
  // either form, or `lvar = rhs` or `lvar op= rhs`.
  static bool ParseSequenceMatchItem(Parser& p, SeqMatchAssign& item) {
    if (AheadIsSubroutineCall(p)) {
      item.call = p.ParseExpr();
      return item.call != nullptr;
    }
    if (p.Check(TokenKind::kPlusPlus) || p.Check(TokenKind::kMinusMinus)) {
      return ParseIncDecMatchItem(p, item, true);
    }
    if (!p.Check(TokenKind::kIdentifier)) return false;
    item.lvar = p.Consume().text;
    if (p.Check(TokenKind::kPlusPlus) || p.Check(TokenKind::kMinusMinus)) {
      return ParseIncDecMatchItem(p, item, false);
    }
    if (!p.Check(TokenKind::kEq) &&
        !IsCompoundAssignToken(p.CurrentToken().kind)) {
      return false;
    }
    item.op = p.Consume().kind;
    item.rhs = p.ParseExpr();
    return item.rhs != nullptr;
  }

  // §16.10: the match items after a group's sequence_expr, each `lvar = rhs`,
  // `lvar op= rhs` or an inc_or_dec_expression, attached to the group's last
  // operand.
  static bool ParseSequenceMatchItems(Parser& p,
                                      std::vector<SeqMatchAssign>& items) {
    while (p.Match(TokenKind::kComma)) {
      SeqMatchAssign item;
      if (!ParseSequenceMatchItem(p, item)) return false;
      items.push_back(item);
    }
    return true;
  }

  // §16.9.2's boolean_abbrev or sequence_abbrev after an operand: `[*n]`,
  // `[*min:max]`, `[*]` and `[+]` for consecutive repetition, `[->n]` and
  // `[->min:max]` for goto, `[=n]` and `[=min:max]` for nonconsecutive, an
  // upper bound of `$` unbounded. Returns false where the brackets hold
  // anything else; `rep` stays kNone where no repetition follows.
  // The count inside a repetition's brackets after its operator: `n`,
  // `min:max` or `min:$`, or nothing for `[*]`.
  static bool ParseRepetitionCount(Parser& p, SeqRepetition& rep) {
    if (p.Match(TokenKind::kRBracket)) {
      if (rep.kind != SeqRepetition::Kind::kConsecutive) return false;
      rep.min = 0;
      rep.max = SeqCycleDelay::kUnbounded;
      return true;
    }
    std::string_view formal;
    if (!ParseSeqDelayBound(p, rep.min, formal, false) || !formal.empty()) {
      return false;
    }
    rep.max = rep.min;
    if (p.Match(TokenKind::kColon)) {
      if (!ParseSeqDelayBound(p, rep.max, formal, true) || !formal.empty()) {
        return false;
      }
    }
    return rep.max >= rep.min && p.Match(TokenKind::kRBracket);
  }

  static bool ParseSequenceRepetition(Parser& p, SeqRepetition& rep) {
    rep = SeqRepetition{};
    if (!AtRepetitionBracket(p)) return true;
    p.Consume();  // '['
    if (p.Match(TokenKind::kPlus)) {
      rep.kind = SeqRepetition::Kind::kConsecutive;
      rep.min = 1;
      rep.max = SeqCycleDelay::kUnbounded;
      return p.Match(TokenKind::kRBracket);
    }
    if (p.Match(TokenKind::kStar)) {
      rep.kind = SeqRepetition::Kind::kConsecutive;
    } else if (p.Match(TokenKind::kArrow)) {
      rep.kind = SeqRepetition::Kind::kGoto;
    } else {
      p.Consume();  // '='
      rep.kind = SeqRepetition::Kind::kNonconsecutive;
    }
    return ParseRepetitionCount(p, rep);
  }

  // §16.9.2: consecutive repetition of a group by an exact count, unrolled
  // as the clause has it, `(a ##2 b)[*3]` being `(a ##2 b) ##1 (a ##2 b) ##1
  // (a ##2 b)`: the group's operands from `first` on are appended again
  // `count - 1` times, the copy's first operand a tick after the last. A
  // range or an unbounded count on a group is not read.
  static bool UnrollGroupRepetition(SeqLinearBody& body, size_t first,
                                    const SeqRepetition& rep) {
    if (rep.kind == SeqRepetition::Kind::kNone) return true;
    if (rep.kind != SeqRepetition::Kind::kConsecutive) return false;
    if (rep.min != rep.max || rep.min == 0) return false;
    // §16.13.1: a group naming a clock of its own is not unrolled.
    if (!body.clocks.empty()) return false;
    size_t n = body.operands.size() - first;
    size_t guards = body.throughouts.size();
    for (uint32_t k = 1; k < rep.min; ++k) {
      for (size_t i = 0; i < n; ++i) {
        body.operands.push_back(body.operands[first + i]);
        SeqCycleDelay delay = body.delays[first + i];
        if (i == 0) {
          delay.min = 1;
          delay.max = 1;
        }
        body.delays.push_back(delay);
        body.match_items.push_back(body.match_items[first + i]);
        body.repetitions.push_back(body.repetitions[first + i]);
      }
      CopyGroupGuards(body, first, guards, n * k);
    }
    return true;
  }

  // §16.9.9: a throughout inside the group, among the first `guards`, spans
  // the copy of the group `shift` operands on as it did the first.
  static void CopyGroupGuards(SeqLinearBody& body, size_t first, size_t guards,
                              size_t shift) {
    for (size_t g = 0; g < guards; ++g) {
      SeqThroughout guard = body.throughouts[g];
      if (guard.first < first) continue;
      guard.first += shift;
      guard.last += shift;
      body.throughouts.push_back(guard);
    }
  }

  // A parenthesised group, `( sequence_expr [, match_items] )`: its operands
  // are read into `body` as the outer operands are, the delay before the group
  // adding to the group's leading delay, and its match items are attached to
  // its last operand.
  static bool ParseSequenceGroup(Parser& p, SeqLinearBody& body,
                                 SeqCycleDelay before,
                                 const std::vector<EventExpr>& clock) {
    p.Expect(TokenKind::kLParen, Subclause("16.10"));
    size_t first = body.operands.size();
    if (!ParseLinearSeqOperandChain(p, body, before, clock)) return false;
    if (body.operands.size() == first) return false;
    if (!ParseSequenceMatchItems(p, body.match_items.back())) return false;
    if (!p.Match(TokenKind::kRParen)) return false;
    SeqRepetition rep;
    if (!ParseSequenceRepetition(p, rep)) return false;
    // §16.10: a repetition of a group holding one unrepeated operand, `(a,
    // x++)[*0:$]`, is that operand's own, its match items performed at each
    // iteration's match, which admits the ranges unrolling does not.
    if (rep.kind != SeqRepetition::Kind::kNone &&
        body.operands.size() == first + 1 &&
        body.repetitions[first].kind == SeqRepetition::Kind::kNone) {
      body.repetitions[first] = rep;
      return true;
    }
    return UnrollGroupRepetition(body, first, rep);
  }

  // §16.13.6: parse the operand chain `[##d0] b0 ##d1 b1 ... ##dn bn` of a
  // linear sequence body, recording each operand and the §16.7 cycle delay
  // before it. `lead` is the delay already owed before the first operand, 0
  // where the body starts with an operand and the delay before a group where
  // the chain is the group's. An operand is a Boolean expression, an instance
  // of a named sequence as §16.8 has it, or a group. Returns false on a delay
  // form the monitor does not read or on a parse failure.
  // Whether the token ends an operand chain: the body's `;` or
  // `endsequence`, a group's `)` or the `,` before its match items, the
  // `intersect`, `and` or `or` before the next operand of those, or the
  // `else` after a property's if branch (§16.12.6).
  static bool AtChainEnd(Parser& p) {
    return p.Check(TokenKind::kKwEndsequence) ||
           p.Check(TokenKind::kSemicolon) || p.Check(TokenKind::kRParen) ||
           p.Check(TokenKind::kComma) || p.Check(TokenKind::kKwOr) ||
           p.Check(TokenKind::kKwAnd) || p.Check(TokenKind::kKwIntersect) ||
           p.Check(TokenKind::kKwWithin) || p.Check(TokenKind::kKwElse) ||
           p.AtEnd();
  }

  // §16.9.9: `exp throughout seq`, exp already read, seq the chain that
  // follows, read into `body` after the delay owed before the throughout,
  // which is where the condition's interval begins; §16.9.1 has throughout
  // bind looser than `##` and tighter than `intersect`, so seq runs to the
  // chain's end. The delay before and seq's leading delay are each one tick
  // count, the interval's start being told from the first operand's delay.
  static bool ParseThroughout(Parser& p, SeqLinearBody& body,
                              SeqCycleDelay before, Expr* cond,
                              const std::vector<EventExpr>& clock) {
    if (before.min != before.max) return false;
    SeqThroughout guard;
    guard.cond = cond;
    guard.first = body.operands.size();
    if (!ParseLinearSeqOperandChain(p, body, before, clock)) return false;
    if (body.operands.size() == guard.first) return false;
    const SeqCycleDelay& lead = body.delays[guard.first];
    if (lead.min != lead.max) return false;
    guard.lead = lead.min - before.min;
    guard.last = body.operands.size() - 1;
    body.throughouts.push_back(guard);
    return true;
  }

  // §16.13.1: the clock the operand just appended is evaluated on, kept
  // parallel to the operands once any chain of the body writes one, the
  // operands before the first written carrying none, the leading clock's.
  static void PushOperandClock(SeqLinearBody& body,
                               const std::vector<EventExpr>& clock) {
    if (clock.empty() && body.clocks.empty()) return;
    while (body.clocks.size() + 1 < body.operands.size()) {
      body.clocks.emplace_back();
    }
    body.clocks.push_back(clock);
  }

  // §16.13.1: `@(event_list)` before an operand, the clock the operands
  // from it on are evaluated on; answers false where the event is
  // malformed, and leaves `clock` as it was where none is written.
  static bool ParseOperandClock(Parser& p, std::vector<EventExpr>& clock) {
    // §16.13.3: of two clocking events juxtaposed the second nullifies the
    // first, so the last written is the one in force.
    while (p.Match(TokenKind::kAt)) {
      if (!p.Match(TokenKind::kLParen)) return false;
      clock = p.ParseEventList();
      if (!p.Match(TokenKind::kRParen) || clock.empty()) return false;
    }
    return true;
  }

  // One operand of a chain with the delay owed before it and the clock it
  // is evaluated on: a group read into `body` as a chain of its own, or a
  // Boolean expression or a sequence instance appended with no match items
  // of its own.
  static bool ParseLinearSeqOperand(Parser& p, SeqLinearBody& body,
                                    SeqCycleDelay before,
                                    const std::vector<EventExpr>& clock) {
    if (AheadIsSequenceGroup(p)) {
      return ParseSequenceGroup(p, body, before, clock);
    }
    Expr* op = AheadIsSequenceInstanceOperand(p)
                   ? ParseSequenceInstanceOperand(p)
                   : p.ParseExpr();
    if (!op) return false;
    if (p.Match(TokenKind::kKwThroughout)) {
      return ParseThroughout(p, body, before, op, clock);
    }
    SeqRepetition rep;
    if (!ParseSequenceRepetition(p, rep)) return false;
    body.operands.push_back(op);
    body.delays.push_back(before);
    body.match_items.emplace_back();
    body.repetitions.push_back(rep);
    PushOperandClock(body, clock);
    return true;
  }

  // The chain's operands under `inherited`, the clock in force where the
  // chain begins, each `@(event_list)` written before an operand, at the
  // chain's start or after a delay, changing it for the operands after.
  static bool ParseLinearSeqOperandChain(
      Parser& p, SeqLinearBody& body, SeqCycleDelay lead,
      const std::vector<EventExpr>& inherited = {}) {
    std::vector<EventExpr> clock = inherited;
    if (!ParseOperandClock(p, clock)) return false;
    SeqCycleDelay next = lead;
    if (p.Match(TokenKind::kHashHash)) {
      SeqCycleDelay written;
      if (!ParseLinearSeqCycleDelay(p, written)) return false;
      next = AddSeqDelays(lead, written);
      if (!ParseOperandClock(p, clock)) return false;
    }
    while (!AtChainEnd(p)) {
      if (!ParseLinearSeqOperand(p, body, next, clock)) return false;
      if (!p.Match(TokenKind::kHashHash)) break;
      if (!ParseLinearSeqCycleDelay(p, next)) return false;
      if (!ParseOperandClock(p, clock)) return false;
    }
    // §16.13.3: the clock in force at the chain's end flows out of it; a
    // group's chain is read before the rest of the chain around it, whose
    // own end writes over this.
    body.clock_out = clock;
    return true;
  }

  // §16.9.10: `seq1 within seq2` abbreviates `(1[*0:$] ##1 seq1 ##1 1[*0:$])
  // intersect seq2`, so the chain seq1 was read into becomes that first
  // operand: a 1 repeated any number of times before it, a tick between, and
  // another after, its own operands' delays and throughouts moved along.
  static void WrapWithinOperand(Parser& p, SeqLinearBody& body) {
    SeqRepetition any;
    any.kind = SeqRepetition::Kind::kConsecutive;
    any.min = 0;
    any.max = SeqCycleDelay::kUnbounded;
    SeqCycleDelay none;
    none.min = 0;
    none.max = 0;
    SeqCycleDelay one;
    one.min = 1;
    one.max = 1;
    SeqLinearBody wrapped;
    wrapped.operands.push_back(OneLiteral(p));
    wrapped.delays.push_back(none);
    wrapped.match_items.emplace_back();
    wrapped.repetitions.push_back(any);
    for (size_t i = 0; i < body.operands.size(); ++i) {
      wrapped.operands.push_back(body.operands[i]);
      wrapped.delays.push_back(i == 0 ? AddSeqDelays(one, body.delays[0])
                                      : body.delays[i]);
      wrapped.match_items.push_back(body.match_items[i]);
      wrapped.repetitions.push_back(body.repetitions[i]);
    }
    wrapped.operands.push_back(OneLiteral(p));
    wrapped.delays.push_back(one);
    wrapped.match_items.emplace_back();
    wrapped.repetitions.push_back(any);
    for (SeqThroughout guard : body.throughouts) {
      guard.first += 1;
      guard.last += 1;
      wrapped.throughouts.push_back(guard);
    }
    body.operands = std::move(wrapped.operands);
    body.delays = std::move(wrapped.delays);
    body.match_items = std::move(wrapped.match_items);
    body.repetitions = std::move(wrapped.repetitions);
    body.throughouts = std::move(wrapped.throughouts);
  }

  // §16.9.1: `intersect` binds tighter than `and` and looser than `##`, so
  // an `intersect` operand is one chain, read to the next `intersect`, `and`
  // or `or`, and the operands after the first are the first's intersects;
  // §16.9.10's `within`, binding tighter still, makes the chain before it
  // the first operand of an intersect with the chain after it.
  static bool ParseLinearSeqIntersection(Parser& p, SeqLinearBody& body) {
    SeqCycleDelay none;
    none.min = 0;
    none.max = 0;
    if (!ParseLinearSeqOperandChain(p, body, none)) return false;
    if (body.operands.empty()) return false;
    if (p.Match(TokenKind::kKwWithin)) {
      // §16.13.1: a chain naming a clock of its own is not wrapped.
      if (!body.clocks.empty()) return false;
      WrapWithinOperand(p, body);
      body.intersects.emplace_back();
      SeqLinearBody& enclosing = body.intersects.back();
      enclosing.locals = body.locals;
      if (!ParseLinearSeqOperandChain(p, enclosing, none)) return false;
      if (enclosing.operands.empty()) return false;
    }
    while (p.Match(TokenKind::kKwIntersect)) {
      body.intersects.emplace_back();
      SeqLinearBody& operand = body.intersects.back();
      operand.locals = body.locals;
      if (!ParseLinearSeqOperandChain(p, operand, none)) return false;
      if (operand.operands.empty()) return false;
    }
    return true;
  }

  // §16.9.1: `and` binds tighter than `or` and looser than `intersect`, so
  // an `and` operand is one chain with its intersects, read to the next
  // `and` or `or`, and the operands after the first are the first's
  // conjuncts.
  static bool ParseLinearSeqConjunction(Parser& p, SeqLinearBody& body) {
    if (!ParseLinearSeqIntersection(p, body)) return false;
    while (p.Match(TokenKind::kKwAnd)) {
      body.conjuncts.emplace_back();
      SeqLinearBody& conjunct = body.conjuncts.back();
      conjunct.locals = body.locals;
      if (!ParseLinearSeqIntersection(p, conjunct)) return false;
    }
    return true;
  }

  // §16.9.1: `or` binds loosest of the sequence operators, so the body is
  // one conjunction per `or` operand, each read to the next `or`, the body's
  // local declarations reaching every chain.
  static bool ParseLinearSeqDisjunction(Parser& p, SeqLinearBody& body) {
    if (!ParseLinearSeqConjunction(p, body)) return false;
    while (p.Match(TokenKind::kKwOr)) {
      body.alternatives.emplace_back();
      SeqLinearBody& alt = body.alternatives.back();
      alt.locals = body.locals;
      if (!ParseLinearSeqConjunction(p, alt)) return false;
    }
    return true;
  }

  // The body's sequence_expr: the `or` operands, or §16.9.8's `first_match (
  // sequence_expr [, match_items] )` around them, whose match items are the
  // operand's own, `first_match(seq, x = e)` being `first_match((seq, x =
  // e))`.
  static bool ParseLinearSeqOperands(Parser& p, ModuleItem* item) {
    SeqLinearBody& body = item->seq_linear;
    if (!p.Match(TokenKind::kKwFirstMatch)) {
      return ParseLinearSeqDisjunction(p, body);
    }
    if (!p.Match(TokenKind::kLParen)) return false;
    body.first_match = true;
    if (!ParseLinearSeqDisjunction(p, body)) return false;
    if (!ParseSequenceMatchItems(p, body.first_match_items)) return false;
    return p.Match(TokenKind::kRParen);
  }
};

// §16.13.6/§9.4.4: trial-parse the simple clocked linear body
// `@(edge clk) b0 ##1 b1 ##1 ... bn` and record the clock + operands so the
// simulator can fire the sequence endpoint on a match. Diagnostics are
// suppressed and the lexer is rewound, so the harvest scan in
// ParseSequenceDecl re-reads the same tokens unchanged; any other body shape
// leaves the fields empty and no monitor is created.
// §16.10 and §16.13.7: the assertion_variable_declarations at the head of
// a named property's body, `logic v = e;`, read as a sequence body's are;
// false where one is malformed.
bool ParserPropertySpecHelpers::ParsePropertyLocalDecls(
    Parser& p, std::vector<SeqLocalDecl>& locals) {
  SeqLinearBody body;
  if (!ParserSeqLinearHelpers::ParseLinearSeqLocalDecls(p, body)) return false;
  locals = std::move(body.locals);
  return true;
}

void Parser::CaptureLinearSequenceBody(ModuleItem* item) {
  auto saved = lexer_.SavePos();
  diag_.PushSuppress();
  in_sequence_body_ = true;
  std::vector<EventExpr> clock;
  bool ok =
      ParserSeqLinearHelpers::ParseLinearSeqLocalDecls(*this, item->seq_linear);
  // §16.8: a sequence declared without a clock inherits one from the sequence
  // or assertion that instantiates it, so a body without a leading `@` is
  // captured as well, with no clock of its own.
  if (ok && Match(TokenKind::kAt)) {
    ok = Match(TokenKind::kLParen);
    if (ok) {
      clock = ParseEventList();
      ok = Match(TokenKind::kRParen);
    }
  }
  if (ok) ok = ParserSeqLinearHelpers::ParseLinearSeqOperands(*this, item);
  // The sequence_expr is terminated by ';' before `endsequence`.
  if (ok) Match(TokenKind::kSemicolon);
  ok = ok && Check(TokenKind::kKwEndsequence) &&
       !item->seq_linear.operands.empty();
  in_sequence_body_ = false;
  diag_.PopSuppress();
  lexer_.RestorePos(saved);
  if (ok) {
    item->seq_clock = std::move(clock);
  } else {
    item->seq_linear = SeqLinearBody{};
  }
}

// §16.12.2: the sequence_expr of a concurrent assertion's property_spec read
// into `item` as a named sequence's body is, for the sequential property the
// assertion evaluates. Answers false, leaving the body empty, where the
// sequence is not one the monitor reads.
bool Parser::ParseSequenceExprInto(ModuleItem* item) {
  uint32_t errors = diag_.ErrorCount() + diag_.SuppressedErrorCount();
  // A sequence read inside another's actual argument leaves the mark as it
  // found it.
  bool was_in_sequence_body = in_sequence_body_;
  in_sequence_body_ = true;
  bool ok = ParserSeqLinearHelpers::ParseLinearSeqOperands(*this, item);
  in_sequence_body_ = was_in_sequence_body;
  // An operand that read with an error, reported or suppressed, is not one.
  if (diag_.ErrorCount() + diag_.SuppressedErrorCount() != errors) ok = false;
  if (!ok || item->seq_linear.operands.empty()) {
    item->seq_linear = SeqLinearBody{};
    return false;
  }
  return true;
}

// §16.12.4 and §16.12.5: one operand of a property's `or` or `and`, read
// as the chain of a sequence with its intersects and within, the `or` and
// `and` after it left for the property level, which §16.12.2 makes the same
// as the sequence's own for two sequences and which reaches a negated or
// boolean operand beside a sequence as well.
bool Parser::ParseSequenceTermInto(ModuleItem* item) {
  uint32_t errors = diag_.ErrorCount() + diag_.SuppressedErrorCount();
  bool was_in_sequence_body = in_sequence_body_;
  in_sequence_body_ = true;
  bool ok = ParserSeqLinearHelpers::ParseLinearSeqIntersection(
      *this, item->seq_linear);
  in_sequence_body_ = was_in_sequence_body;
  if (diag_.ErrorCount() + diag_.SuppressedErrorCount() != errors) ok = false;
  if (!ok || item->seq_linear.operands.empty()) {
    item->seq_linear = SeqLinearBody{};
    return false;
  }
  return true;
}

}  // namespace delta
