#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "parser/parser.h"
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

  // Whether the tokens ahead are a parenthesised group holding a `##` or a `,`
  // at its own depth: a sub-sequence, or §16.10's `( sequence_expr ,
  // sequence_match_item ... )`, either of which ParseExpr cannot read. The
  // lexer is rewound.
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
          (p.Check(TokenKind::kHashHash) || p.Check(TokenKind::kComma))) {
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

  // §16.8.1: an actual for a formal of type event is an event_expression, so
  // one opening with an edge keyword is kept as the edge over its signal, a
  // unary expression whose operator is the keyword, for the flattening to read
  // as the instantiated sequence's clock; an actual with no edge is an ordinary
  // expression, which an `@(posedge sig)` over a formal sig takes as the
  // signal.
  static Expr* ParseSequenceActualArg(Parser& p) {
    if (p.Check(TokenKind::kDollar)) {
      Token tok = p.Consume();
      auto* dollar = p.arena_.Create<Expr>();
      dollar->kind = ExprKind::kIdentifier;
      dollar->text = tok.text;
      dollar->range.start = tok.loc;
      return dollar;
    }
    if (p.Check(TokenKind::kKwPosedge) || p.Check(TokenKind::kKwNegedge) ||
        p.Check(TokenKind::kKwEdge)) {
      Token edge = p.Consume();
      auto* event = p.arena_.Create<Expr>();
      event->kind = ExprKind::kUnary;
      event->op = edge.kind;
      event->text = edge.text;
      event->range.start = edge.loc;
      event->lhs = p.ParseExpr();
      return event;
    }
    return p.ParseExpr();
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

  // §16.10: the match items after a group's sequence_expr, each `lvar = rhs`
  // or `lvar op= rhs`, attached to the group's last operand.
  static bool ParseSequenceMatchItems(Parser& p,
                                      std::vector<SeqMatchAssign>& items) {
    while (p.Match(TokenKind::kComma)) {
      if (!p.Check(TokenKind::kIdentifier)) return false;
      SeqMatchAssign item;
      item.lvar = p.Consume().text;
      if (!p.Check(TokenKind::kEq) &&
          !IsCompoundAssignToken(p.CurrentToken().kind)) {
        return false;
      }
      item.op = p.Consume().kind;
      item.rhs = p.ParseExpr();
      if (item.rhs == nullptr) return false;
      items.push_back(item);
    }
    return true;
  }

  // A parenthesised group, `( sequence_expr [, match_items] )`: its operands
  // are read into `body` as the outer operands are, the delay before the group
  // adding to the group's leading delay, and its match items are attached to
  // its last operand.
  static bool ParseSequenceGroup(Parser& p, SeqLinearBody& body,
                                 SeqCycleDelay before) {
    p.Expect(TokenKind::kLParen, Subclause("16.10"));
    size_t first = body.operands.size();
    if (!ParseLinearSeqOperandChain(p, body, before)) return false;
    if (body.operands.size() == first) return false;
    if (!ParseSequenceMatchItems(p, body.match_items.back())) return false;
    return p.Match(TokenKind::kRParen);
  }

  // §16.13.6: parse the operand chain `[##d0] b0 ##d1 b1 ... ##dn bn` of a
  // linear sequence body, recording each operand and the §16.7 cycle delay
  // before it. `lead` is the delay already owed before the first operand, 0
  // where the body starts with an operand and the delay before a group where
  // the chain is the group's. An operand is a Boolean expression, an instance
  // of a named sequence as §16.8 has it, or a group. Returns false on a delay
  // form the monitor does not read or on a parse failure.
  // Whether the token ends an operand chain: the body's `;` or
  // `endsequence`, a group's `)` or the `,` before its match items, or the
  // `and` or `or` before the next operand of those.
  static bool AtChainEnd(Parser& p) {
    return p.Check(TokenKind::kKwEndsequence) ||
           p.Check(TokenKind::kSemicolon) || p.Check(TokenKind::kRParen) ||
           p.Check(TokenKind::kComma) || p.Check(TokenKind::kKwOr) ||
           p.Check(TokenKind::kKwAnd) || p.AtEnd();
  }

  // One operand of a chain with the delay owed before it: a group read into
  // `body` as a chain of its own, or a Boolean expression or a sequence
  // instance appended with no match items of its own.
  static bool ParseLinearSeqOperand(Parser& p, SeqLinearBody& body,
                                    SeqCycleDelay before) {
    if (AheadIsSequenceGroup(p)) return ParseSequenceGroup(p, body, before);
    Expr* op = AheadIsSequenceInstanceOperand(p)
                   ? ParseSequenceInstanceOperand(p)
                   : p.ParseExpr();
    if (!op) return false;
    body.operands.push_back(op);
    body.delays.push_back(before);
    body.match_items.emplace_back();
    return true;
  }

  static bool ParseLinearSeqOperandChain(Parser& p, SeqLinearBody& body,
                                         SeqCycleDelay lead) {
    SeqCycleDelay next = lead;
    if (p.Match(TokenKind::kHashHash)) {
      SeqCycleDelay written;
      if (!ParseLinearSeqCycleDelay(p, written)) return false;
      next = AddSeqDelays(lead, written);
    }
    while (!AtChainEnd(p)) {
      if (!ParseLinearSeqOperand(p, body, next)) return false;
      if (!p.Match(TokenKind::kHashHash)) break;
      if (!ParseLinearSeqCycleDelay(p, next)) return false;
    }
    return true;
  }

  // §16.9.1: `or` binds loosest of the sequence operators, so the body is
  // one chain per `or` operand, each read to the next `or`, the body's local
  // declarations reaching every chain.
  // §16.9.1: `and` binds tighter than `or` and looser than `##`, so an `and`
  // operand is one chain, read to the next `and` or `or`, and the operands
  // after the first are the first's conjuncts.
  static bool ParseLinearSeqConjunction(Parser& p, SeqLinearBody& body) {
    SeqCycleDelay none;
    none.min = 0;
    none.max = 0;
    if (!ParseLinearSeqOperandChain(p, body, none)) return false;
    if (body.operands.empty()) return false;
    while (p.Match(TokenKind::kKwAnd)) {
      body.conjuncts.emplace_back();
      SeqLinearBody& conjunct = body.conjuncts.back();
      conjunct.locals = body.locals;
      if (!ParseLinearSeqOperandChain(p, conjunct, none)) return false;
      if (conjunct.operands.empty()) return false;
    }
    return true;
  }

  // §16.9.1: `or` binds loosest of the sequence operators, so the body is
  // one conjunction per `or` operand, each read to the next `or`, the body's
  // local declarations reaching every chain.
  static bool ParseLinearSeqOperands(Parser& p, ModuleItem* item) {
    SeqLinearBody& body = item->seq_linear;
    if (!ParseLinearSeqConjunction(p, body)) return false;
    while (p.Match(TokenKind::kKwOr)) {
      body.alternatives.emplace_back();
      SeqLinearBody& alt = body.alternatives.back();
      alt.locals = body.locals;
      if (!ParseLinearSeqConjunction(p, alt)) return false;
    }
    return true;
  }
};

// §16.13.6/§9.4.4: trial-parse the simple clocked linear body
// `@(edge clk) b0 ##1 b1 ##1 ... bn` and record the clock + operands so the
// simulator can fire the sequence endpoint on a match. Diagnostics are
// suppressed and the lexer is rewound, so the harvest scan in
// ParseSequenceDecl re-reads the same tokens unchanged; any other body shape
// leaves the fields empty and no monitor is created.
void Parser::CaptureLinearSequenceBody(ModuleItem* item) {
  auto saved = lexer_.SavePos();
  diag_.PushSuppress();
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
  diag_.PopSuppress();
  lexer_.RestorePos(saved);
  if (ok) {
    item->seq_clock = std::move(clock);
  } else {
    item->seq_linear = SeqLinearBody{};
  }
}

}  // namespace delta
