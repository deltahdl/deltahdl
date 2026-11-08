#include <cstddef>
#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/linear_sequence_body.h"
#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"
#include "parser/parser_sequence_property_decl_internal.h"

namespace delta {

bool Parser::AtDollarEndingRange() {
  if (!Check(TokenKind::kDollar)) return false;
  auto saved = lexer_.SavePos();
  Consume();
  const bool kEnds = Check(TokenKind::kRBracket);
  lexer_.RestorePos(saved);
  return kEnds;
}

struct ParserSeqLinearHelpers {
  static bool ParseSeqDelayBound(Parser& p, uint32_t& val, Expr*& expr,
                                 bool dollar, bool bracketed) {
    if (p.Check(TokenKind::kIntLiteral)) {
      val = ParseSeqDelayLiteral(p);
      return true;
    }
    if (dollar && p.AtDollarEndingRange()) {
      p.Consume();
      val = SeqCycleDelay::kUnbounded;
      return true;
    }
    if ((p.Check(TokenKind::kIdentifier) || p.Check(TokenKind::kDollar)) &&
        !bracketed) {
      Token tok = p.Consume();
      expr = p.arena_.Create<Expr>();
      expr->kind = ExprKind::kIdentifier;
      expr->text = tok.text;
      expr->range.start = tok.loc;
      return true;
    }
    if (!bracketed && !p.Match(TokenKind::kLParen)) return false;
    expr = p.ParseExpr();
    if (!bracketed) p.Match(TokenKind::kRParen);
    return true;
  }

  static bool BoundsOrdered(const SeqCycleDelay& bounds) {
    return bounds.min_expr != nullptr || bounds.max_expr != nullptr ||
           bounds.max >= bounds.min;
  }

  static bool ParseLinearSeqCycleDelay(Parser& p, SeqCycleDelay& delay) {
    delay = SeqCycleDelay{};
    if (!p.Check(TokenKind::kLBracket)) {
      if (!ParseSeqDelayBound(p, delay.min, delay.min_expr, false, false)) {
        return false;
      }
      delay.max = delay.min;
      delay.max_expr = delay.min_expr;
      return true;
    }
    p.Consume();
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
    if (!ParseSeqDelayBound(p, delay.min, delay.min_expr, false, true)) {
      return false;
    }
    if (!p.Match(TokenKind::kColon)) return false;
    if (!ParseSeqDelayBound(p, delay.max, delay.max_expr, true, true)) {
      return false;
    }
    return BoundsOrdered(delay) && p.Match(TokenKind::kRBracket);
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

  static void SkipToMatchingParen(Parser& p) {
    int depth = 1;
    while (depth > 0 && !p.AtEnd()) {
      if (p.Check(TokenKind::kLParen)) ++depth;
      if (p.Check(TokenKind::kRParen)) --depth;
      p.Consume();
    }
  }

  static bool AtRepetitionBracket(Parser& p) {
    if (!p.Check(TokenKind::kLBracket)) return false;
    auto saved = p.lexer_.SavePos();
    p.Consume();
    bool repetition = p.Check(TokenKind::kStar) || p.Check(TokenKind::kArrow) ||
                      p.Check(TokenKind::kEq) || p.Check(TokenKind::kPlus);
    p.lexer_.RestorePos(saved);
    return repetition;
  }

  static bool AtSequenceOperator(Parser& p) {
    return p.Check(TokenKind::kKwAnd) || p.Check(TokenKind::kKwOr) ||
           p.Check(TokenKind::kKwIntersect) || p.Check(TokenKind::kKwWithin);
  }

  static bool AtSequenceToken(Parser& p) {
    return p.Check(TokenKind::kHashHash) || p.Check(TokenKind::kComma) ||
           p.Check(TokenKind::kKwThroughout) || AtRepetitionBracket(p) ||
           AtSequenceOperator(p) || AtClockingEvent(p);
  }

  static bool AtClockingEvent(Parser& p) { return p.Check(TokenKind::kAt); }

  static bool SkipGroupHolding(Parser& p, bool (*at)(Parser&), bool nested) {
    p.Consume();
    int depth = 1;
    bool holds = false;
    while (depth > 0 && !p.AtEnd()) {
      if (p.Check(TokenKind::kLParen)) ++depth;
      if (p.Check(TokenKind::kRParen)) --depth;
      if ((depth == 1 || (nested && depth > 1)) && at(p)) holds = true;
      p.Consume();
    }
    return holds;
  }

  static bool AheadGroupHolds(Parser& p, bool (*at)(Parser&)) {
    if (!p.Check(TokenKind::kLParen)) return false;
    auto saved = p.lexer_.SavePos();
    bool holds = SkipGroupHolding(p, at, false);
    p.lexer_.RestorePos(saved);
    return holds;
  }

  static bool AtChainToken(Parser& p) {
    return p.Check(TokenKind::kHashHash) || p.Check(TokenKind::kKwThroughout) ||
           AtRepetitionBracket(p);
  }

  static bool AheadIsSequenceGroup(Parser& p) {
    return AheadGroupHolds(p, AtSequenceToken);
  }

  static Expr* ParseSequenceInstanceOperand(Parser& p) {
    Token name = p.Consume();
    auto* call = p.arena_.Create<Expr>();
    call->kind = ExprKind::kCall;
    call->callee = name.text;
    call->text = name.text;
    call->range.start = name.loc;
    p.Expect(TokenKind::kLParen, Subclause("16.8"));
    bool named = false;
    while (!p.Check(TokenKind::kRParen) && !p.AtEnd()) {
      if (p.Check(TokenKind::kDot)) {
        named = true;
        p.Consume();
        call->arg_names.push_back(
            p.Expect(TokenKind::kIdentifier, Subclause("16.8")).text);
        p.Expect(TokenKind::kLParen, Subclause("16.8"));
        call->args.push_back(ParseSequenceActualArg(p));
        p.Expect(TokenKind::kRParen, Subclause("16.8"));
      } else if (named) {
        return nullptr;
      } else {
        call->args.push_back(ParseSequenceActualArg(p));
      }
      if (!p.Match(TokenKind::kComma)) break;
      if (named && p.Check(TokenKind::kRParen)) return nullptr;
    }
    p.Expect(TokenKind::kRParen, Subclause("16.8"));
    return call;
  }

  static Expr* ParseSequenceActualArg(Parser& p) {
    bool plain = true;
    return ParserPropertySpecHelpers::ParsePropertyActualArg(p, plain);
  }

  static void ParseLocalType(Parser& p, SeqLocalDecl& typed) {
    if (p.Match(TokenKind::kKwVar) && !VarWritesDataType(p.lexer_)) {
      typed.type_kw = TokenKind::kKwLogic;
    } else if (p.Check(TokenKind::kIdentifier)) {
      typed.named_type = p.ParseNamedType();
    } else {
      typed.type_kw = p.Consume().kind;
    }
    if (p.Check(TokenKind::kKwSigned) || p.Check(TokenKind::kKwUnsigned)) {
      typed.signing = p.Consume().kind;
    }
    DataType packed;
    p.ParsePackedDims(packed);
    if (packed.packed_dim_left != nullptr) {
      typed.packed_dims.emplace_back(packed.packed_dim_left,
                                     packed.packed_dim_right);
    }
    typed.packed_dims.insert(typed.packed_dims.end(),
                             packed.extra_packed_dims.begin(),
                             packed.extra_packed_dims.end());
  }

  static bool ParseLinearSeqLocalDecls(Parser& p, SeqLinearBody& body) {
    while (AtAssertionVariableDecl(p.lexer_, p.known_types_)) {
      SeqLocalDecl typed;
      ParseLocalType(p, typed);
      do {
        if (!p.Check(TokenKind::kIdentifier)) return false;
        SeqLocalDecl local = typed;
        local.name = p.Consume().text;
        if (p.Match(TokenKind::kEq)) local.init = p.ParseExpr();
        body.locals.push_back(local);
      } while (p.Match(TokenKind::kComma));
      if (!p.Match(TokenKind::kSemicolon)) return false;
    }
    return true;
  }

  static bool ParseRepetitionCount(Parser& p, SeqRepetition& rep) {
    if (p.Match(TokenKind::kRBracket)) {
      if (rep.kind != SeqRepetition::Kind::kConsecutive) return false;
      rep.min = 0;
      rep.max = SeqCycleDelay::kUnbounded;
      return true;
    }
    if (!ParseSeqDelayBound(p, rep.min, rep.min_expr, false, true)) {
      return false;
    }
    rep.max = rep.min;
    rep.max_expr = rep.min_expr;
    if (p.Match(TokenKind::kColon)) {
      rep.max_expr = nullptr;
      if (!ParseSeqDelayBound(p, rep.max, rep.max_expr, true, true)) {
        return false;
      }
    }
    return BoundsOrdered(rep) && p.Match(TokenKind::kRBracket);
  }

  static bool ParseSequenceRepetition(Parser& p, SeqRepetition& rep) {
    rep = SeqRepetition{};
    if (!AtRepetitionBracket(p)) return true;
    p.Consume();
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
      p.Consume();
      rep.kind = SeqRepetition::Kind::kNonconsecutive;
    }
    return ParseRepetitionCount(p, rep);
  }

  static void AppendOperand(SeqLinearBody& body, Expr* op, SeqCycleDelay before,
                            const SeqRepetition& rep,
                            const std::vector<EventExpr>& clock) {
    body.operands.push_back(op);
    body.delays.push_back(before);
    body.match_items.emplace_back();
    body.repetitions.push_back(rep);
    PushOperandClock(body, clock);
  }

  static Expr* NestedGroupHolder(Parser& p, ModuleItem*& inner) {
    SourceLoc loc = p.CurrentLoc();
    inner = p.arena_.Create<ModuleItem>();
    inner->kind = ModuleItemKind::kSequenceDecl;
    inner->loc = loc;
    auto* tree = p.arena_.Create<PropertyExprNode>();
    tree->kind = PropertyExprNode::Kind::kSequence;
    tree->sequence = inner;
    Expr* holder =
        ParserPropertySpecHelpers::PropertySpecPlaceholder(p.arena_, loc);
    holder->property_actual = tree;
    return holder;
  }

  static bool ParseNestedGroup(Parser& p, SeqLinearBody& body,
                               SeqCycleDelay before,
                               const std::vector<EventExpr>& clock) {
    ModuleItem* inner = nullptr;
    Expr* holder = NestedGroupHolder(p, inner);
    p.Consume();
    SeqRepetition rep;
    std::vector<SeqMatchAssign> items;
    bool ok = ParseLinearSeqOperands(p, inner) &&
              ParserPropertySpecHelpers::ParseSequenceMatchItems(p, items) &&
              p.Match(TokenKind::kRParen) && ParseSequenceRepetition(p, rep);
    AppendOperand(body, holder, before, rep, clock);
    body.match_items.back() = std::move(items);
    return ok;
  }

  static void AttachGroupItems(Parser& p, SeqLinearBody& body,
                               const std::vector<SeqMatchAssign>& items) {
    if (items.empty()) return;
    if (body.repetitions.back().kind != SeqRepetition::Kind::kNone) {
      Expr* one = ParserPropertySpecHelpers::OneLiteral(p);
      one->range.start = body.operands.back()->range.start;
      const std::vector<EventExpr> kClock =
          body.clocks.size() == body.operands.size() ? body.clocks.back()
                                                     : std::vector<EventExpr>{};
      SeqCycleDelay fused;
      fused.min = 0;
      fused.max = 0;
      AppendOperand(body, one, fused, SeqRepetition{}, kClock);
    }
    std::vector<SeqMatchAssign>& last = body.match_items.back();
    last.insert(last.end(), items.begin(), items.end());
  }

  static bool ReadGroupInto(Parser& p, SeqLinearBody& body,
                            SeqCycleDelay before,
                            const std::vector<EventExpr>& clock,
                            SeqRepetition& rep) {
    p.Expect(TokenKind::kLParen, Subclause("16.10"));
    size_t first = body.operands.size();
    if (!ParseLinearSeqOperandChain(p, body, before, clock)) return false;
    if (body.operands.size() == first) return false;
    std::vector<SeqMatchAssign> items;
    if (!ParserPropertySpecHelpers::ParseSequenceMatchItems(p, items)) {
      return false;
    }
    MarkEmptyMatchItems(body, first, items);
    AttachGroupItems(p, body, items);
    if (!p.Match(TokenKind::kRParen)) return false;
    return ParseSequenceRepetition(p, rep);
  }

  static bool AheadIsGroupReadWhole(Parser& p) {
    auto saved = p.lexer_.SavePos();
    p.diag_.PushSuppress();
    bool clocked = SkipGroupHolding(p, AtClockingEvent, true);
    p.lexer_.RestorePos(saved);
    bool chain = SkipGroupHolding(p, AtChainToken, true);
    SeqRepetition rep;
    ParseSequenceRepetition(p, rep);
    p.diag_.PopSuppress();
    p.lexer_.RestorePos(saved);
    return (chain && rep.IteratesWhole()) ||
           (clocked && rep.kind == SeqRepetition::Kind::kConsecutive);
  }

  static bool ParseRepeatedGroup(Parser& p, SeqLinearBody& body,
                                 SeqCycleDelay before,
                                 const std::vector<EventExpr>& clock) {
    ModuleItem* inner = nullptr;
    Expr* holder = NestedGroupHolder(p, inner);
    SeqCycleDelay none;
    none.min = 0;
    none.max = 0;
    SeqRepetition rep;
    bool ok = ReadGroupInto(p, inner->seq_linear, none, {}, rep);
    AppendOperand(body, holder, before, rep, clock);
    return ok;
  }

  static bool ParseSequenceGroup(Parser& p, SeqLinearBody& body,
                                 SeqCycleDelay before,
                                 const std::vector<EventExpr>& clock) {
    if (AheadGroupHolds(p, AtSequenceOperator)) {
      return ParseNestedGroup(p, body, before, clock);
    }
    if (AheadIsGroupReadWhole(p)) {
      return ParseRepeatedGroup(p, body, before, clock);
    }
    size_t first = body.operands.size();
    SeqRepetition rep;
    if (!ReadGroupInto(p, body, before, clock, rep)) return false;
    if (rep.kind != SeqRepetition::Kind::kNone &&
        body.operands.size() == first + 1 &&
        body.repetitions[first].kind == SeqRepetition::Kind::kNone) {
      body.repetitions[first] = rep;
      return true;
    }
    return UnrollGroupRepetition(body, first, rep);
  }

  static bool AtChainEnd(Parser& p) {
    return p.Check(TokenKind::kKwEndsequence) ||
           p.Check(TokenKind::kSemicolon) || p.Check(TokenKind::kRParen) ||
           p.Check(TokenKind::kComma) || p.Check(TokenKind::kKwOr) ||
           p.Check(TokenKind::kKwAnd) || p.Check(TokenKind::kKwIntersect) ||
           p.Check(TokenKind::kKwWithin) || p.Check(TokenKind::kKwElse) ||
           p.AtEnd();
  }

  static bool ParseThroughout(Parser& p, SeqLinearBody& body,
                              SeqCycleDelay before, Expr* cond,
                              const std::vector<EventExpr>& clock) {
    SeqThroughout guard;
    guard.cond = cond;
    guard.first = body.operands.size();
    if (before.min != before.max) {
      AppendOperand(body, ParserPropertySpecHelpers::OneLiteral(p), before,
                    SeqRepetition{}, clock);
      guard.begins_at_read = true;
      before = SeqCycleDelay{};
      before.min = 0;
      before.max = 0;
    }
    size_t seq_first = body.operands.size();
    if (!ParseLinearSeqOperandChain(p, body, before, clock)) return false;
    if (body.operands.size() == seq_first) return false;
    if (!guard.begins_at_read) {
      guard.lead = body.delays[seq_first].min - before.min;
    }
    guard.last = body.operands.size() - 1;
    body.throughouts.push_back(guard);
    return true;
  }

  static bool ParseOperandClock(Parser& p, std::vector<EventExpr>& clock) {
    while (p.Match(TokenKind::kAt)) {
      if (!p.Match(TokenKind::kLParen)) {
        clock = {p.ParseNamedClockingEvent()};
        continue;
      }
      clock = p.ParseEventList();
      if (!p.Match(TokenKind::kRParen) || clock.empty()) return false;
    }
    return true;
  }

  static bool ParseLinearSeqOperand(Parser& p, SeqLinearBody& body,
                                    SeqCycleDelay before,
                                    const std::vector<EventExpr>& clock) {
    if (AheadIsSequenceGroup(p)) {
      return ParseSequenceGroup(p, body, before, clock);
    }
    Expr* op = AheadIsSequenceInstanceOperand(p)
                   ? ParseSequenceInstanceOperand(p)
                   : ParserPropertySpecHelpers::ParseExpressionOrDist(p);
    if (!op) return false;
    if (p.Match(TokenKind::kKwThroughout)) {
      return ParseThroughout(p, body, before, op, clock);
    }
    SeqRepetition rep;
    if (!ParseSequenceRepetition(p, rep)) return false;
    AppendOperand(body, op, before, rep, clock);
    return true;
  }

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
      next.written = true;
      if (!ParseOperandClock(p, clock)) return false;
    }
    while (!AtChainEnd(p)) {
      if (!ParseLinearSeqOperand(p, body, next, clock)) return false;
      if (!p.Match(TokenKind::kHashHash)) break;
      if (!ParseLinearSeqCycleDelay(p, next)) return false;
      if (!ParseOperandClock(p, clock)) return false;
    }
    body.clock_out = clock;
    return true;
  }

  static bool ParseLinearSeqIntersection(Parser& p, SeqLinearBody& body) {
    SeqCycleDelay none;
    none.min = 0;
    none.max = 0;
    if (!ParseLinearSeqOperandChain(p, body, none)) return false;
    if (body.operands.empty()) return false;
    if (p.Match(TokenKind::kKwWithin)) {
      WrapWithinOperand(body, ParserPropertySpecHelpers::OneLiteral(p),
                        ParserPropertySpecHelpers::OneLiteral(p));
      body.within = true;
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

  static bool ParseLinearSeqOperands(Parser& p, ModuleItem* item) {
    SeqLinearBody& body = item->seq_linear;
    if (!p.Match(TokenKind::kKwFirstMatch)) {
      return ParseLinearSeqDisjunction(p, body);
    }
    if (!p.Match(TokenKind::kLParen)) return false;
    body.first_match = true;
    if (!ParseLinearSeqDisjunction(p, body)) return false;
    if (!ParserPropertySpecHelpers::ParseSequenceMatchItems(
            p, body.first_match_items))
      return false;
    return p.Match(TokenKind::kRParen);
  }
};

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
  if (ok && Match(TokenKind::kAt)) {
    if (Match(TokenKind::kLParen)) {
      clock = ParseEventList();
      ok = Match(TokenKind::kRParen);
    } else {
      clock.push_back(ParseNamedClockingEvent());
    }
  }
  bool clock_read = ok;
  if (ok) ok = ParserSeqLinearHelpers::ParseLinearSeqOperands(*this, item);
  if (ok) Match(TokenKind::kSemicolon);
  ok = ok && Check(TokenKind::kKwEndsequence) &&
       !item->seq_linear.operands.empty();
  in_sequence_body_ = false;
  diag_.PopSuppress();
  lexer_.RestorePos(saved);
  if (clock_read) item->seq_clock = std::move(clock);
  if (!ok) item->seq_linear = SeqLinearBody{};
}

bool Parser::ParseSequenceExprInto(ModuleItem* item) {
  uint32_t errors = diag_.ErrorCount() + diag_.SuppressedErrorCount();
  bool was_in_sequence_body = in_sequence_body_;
  in_sequence_body_ = true;
  bool ok = ParserSeqLinearHelpers::ParseLinearSeqOperands(*this, item);
  in_sequence_body_ = was_in_sequence_body;
  if (diag_.ErrorCount() + diag_.SuppressedErrorCount() != errors) ok = false;
  if (!ok || item->seq_linear.operands.empty()) {
    item->seq_linear = SeqLinearBody{};
    return false;
  }
  return true;
}

bool Parser::ParseSequenceTermInto(ModuleItem* item) {
  uint32_t errors = diag_.ErrorCount() + diag_.SuppressedErrorCount();
  bool was_in_sequence_body = in_sequence_body_;
  in_sequence_body_ = true;
  bool ok = Check(TokenKind::kKwFirstMatch)
                ? ParserSeqLinearHelpers::ParseLinearSeqOperands(*this, item)
                : ParserSeqLinearHelpers::ParseLinearSeqIntersection(
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
