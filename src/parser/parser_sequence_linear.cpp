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

// §16.13.6/§9.4.4: the trial parse that captures a sequence body's linear form
// for the simulator's sequence monitor, held apart from the Parser's own
// methods as the other helper structs are, so the declarations the parser
// header carries stay within the gate on its length.
struct ParserSeqLinearHelpers {
  // One bound of §16.7's cycle_delay_range as the linear monitor reads it: an
  // integer literal, `$` where the caller admits it, or a constant expression
  // kept for the instantiation and the elaboration-time constants to settle
  // (§16.8): a name, a parenthesized constant_primary, or, between brackets,
  // any constant_expression. Returns false for any other form, which leaves
  // the sequence without a monitor as before.
  static bool ParseSeqDelayBound(Parser& p, uint32_t& val, Expr*& expr,
                                 bool dollar, bool bracketed) {
    if (p.Check(TokenKind::kIntLiteral)) {
      val = ParseSeqDelayLiteral(p);
      return true;
    }
    if (dollar && p.Match(TokenKind::kDollar)) {
      val = SeqCycleDelay::kUnbounded;
      return true;
    }
    if (p.Check(TokenKind::kIdentifier) && !bracketed) {
      Token tok = p.Consume();
      expr = p.arena_.Create<Expr>();
      expr->kind = ExprKind::kIdentifier;
      expr->text = tok.text;
      expr->range.start = tok.loc;
      return true;
    }
    // The syntax was checked as the body was scanned (§16.7), so a bound
    // read here is one the parse admitted.
    if (!bracketed && !p.Match(TokenKind::kLParen)) return false;
    expr = p.ParseExpr();
    if (!bracketed) p.Match(TokenKind::kRParen);
    return true;
  }

  // §16.7 and §16.9.2: whether a range's bounds are in order, a bound written
  // as an expression left to the elaborator's check.
  static bool BoundsOrdered(const SeqCycleDelay& bounds) {
    return bounds.min_expr != nullptr || bounds.max_expr != nullptr ||
           bounds.max >= bounds.min;
  }

  // §16.7's cycle_delay_range after its `##`: a constant_primary N for [N:N], a
  // bracketed `a:b` or `a:$`, and the two abbreviations `[*]` for [0:$] and
  // `[+]` for [1:$]. Returns false where the delay is not one of these.
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

  // Whether the token is §16.9's `and`, `or`, `intersect` or `within`, an
  // operator joining two sequences that no expression has.
  static bool AtSequenceOperator(Parser& p) {
    return p.Check(TokenKind::kKwAnd) || p.Check(TokenKind::kKwOr) ||
           p.Check(TokenKind::kKwIntersect) || p.Check(TokenKind::kKwWithin);
  }

  // Whether the token is a `##`, a `,`, a `throughout`, a repetition, a
  // sequence operator or the `@` of a clocking event (§16.13.1), which only a
  // sequence holds.
  static bool AtSequenceToken(Parser& p) {
    return p.Check(TokenKind::kHashHash) || p.Check(TokenKind::kComma) ||
           p.Check(TokenKind::kKwThroughout) || AtRepetitionBracket(p) ||
           AtSequenceOperator(p) || AtClockingEvent(p);
  }

  // Whether the token is the `@` opening a clocking event.
  static bool AtClockingEvent(Parser& p) { return p.Check(TokenKind::kAt); }

  // Consumes the parenthesised group at the cursor, answering whether it
  // holds a token `at` answers true for: at its own depth, or at any depth
  // inside it where `nested` says so.
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

  // Whether the tokens ahead are a parenthesised group holding, at its own
  // depth, a token `at` answers true for. The lexer is rewound.
  static bool AheadGroupHolds(Parser& p, bool (*at)(Parser&)) {
    if (!p.Check(TokenKind::kLParen)) return false;
    auto saved = p.lexer_.SavePos();
    bool holds = SkipGroupHolding(p, at, false);
    p.lexer_.RestorePos(saved);
    return holds;
  }

  // Whether the token is a `##`, a `throughout` or a repetition, any of which
  // makes the group holding it more than one operand or a repeated one.
  static bool AtChainToken(Parser& p) {
    return p.Check(TokenKind::kHashHash) || p.Check(TokenKind::kKwThroughout) ||
           AtRepetitionBracket(p);
  }

  // Whether the tokens ahead are a parenthesised group holding a `##`, a `,`,
  // a `throughout`, a repetition or a sequence operator at its own depth: a
  // sub-sequence, §16.10's `( sequence_expr , sequence_match_item ... )`,
  // §16.9.9's condition over one or a repeated operand in parentheses, none
  // of which ParseExpr can read. The lexer is rewound.
  static bool AheadIsSequenceGroup(Parser& p) {
    return AheadGroupHolds(p, AtSequenceToken);
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
    // A.2.10's sequence_list_of_arguments takes no positional actual, an
    // empty one included, after a named one, so the operand is not read
    // where one follows.
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

  // §16.10 with §6.18, §6.11 and §7.4.1: a local's var_data_type, into
  // `typed`: its type keyword or the type name written in its place, with the
  // package or class scope A.2.2.1 lets it stand behind, then the signing
  // keyword and the packed dimensions written after it, each dimension a left
  // and a right bound in the order written. A.2.2.1 lets `var` open it, and
  // §6.8 has one written with no data type after the `var` be logic.
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

  // §16.10 Syntax 16-13: the assertion_variable_declarations a sequence body
  // opens with, each `type [signing] [packed dimensions] name [= init] {,
  // name [= init]} ;` over a data type keyword, its var_data_type taking the
  // signing keyword §6.11 and the packed dimensions §7.4.1 write after the
  // keyword, or over a type name in the keyword's place (§6.18), recorded as
  // the body's local variables, each declared name of the type written. A
  // declaration in any other shape ends the capture.
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

  // §16.9.2's boolean_abbrev or sequence_abbrev after an operand: `[*n]`,
  // `[*min:max]`, `[*]` and `[+]` for consecutive repetition, `[->n]` and
  // `[->min:max]` for goto, `[=n]` and `[=min:max]` for nonconsecutive, an
  // upper bound of `$` unbounded. Returns false where the brackets hold
  // anything else; `rep` stays kNone where no repetition follows.
  // The count inside a repetition's brackets after its operator: `n`,
  // `min:max` or `min:$`, each bound read as a delay's is, or nothing for
  // `[*]`.
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

  // One operand of a chain, the delay owed before it, its repetition and the
  // clock it is evaluated on, appended to `body` with no match items of its
  // own.
  static void AppendOperand(SeqLinearBody& body, Expr* op, SeqCycleDelay before,
                            const SeqRepetition& rep,
                            const std::vector<EventExpr>& clock) {
    body.operands.push_back(op);
    body.delays.push_back(before);
    body.match_items.emplace_back();
    body.repetitions.push_back(rep);
    PushOperandClock(body, clock);
  }

  // The placeholder standing as one operand of a chain for the group at the
  // cursor, read into `inner`, a sequence of its own, as a sequence bound to a
  // formal of type sequence is (§16.8.1).
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

  // §16.9.5 to §16.9.7 and §16.9.10: a group holding `and`, `or`,
  // `intersect` or `within` at its own depth does not splice into the chain
  // around it, so its sequence_expr is read into a sequence of its own, which
  // stands as one operand of the chain through a placeholder carrying it, as
  // a sequence bound to a formal of type sequence does (§16.8.1). §16.10: the
  // group's match items, performed at each match of that sequence_expr, are
  // the operand's own.
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

  // §16.10 and §16.11: a group's match items run once, at each match of its
  // sequence_expr. Kept on a last operand that repeats, `(b[*2], x++)` or
  // `(b[->2], x++)`, they would run at each repetition, so they go to the
  // literal 1 fused to its end, on its clock, as `b[*2] ##0 (1, x++)` has
  // them; otherwise to the last operand.
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

  // A parenthesised group, `( sequence_expr [, match_items] )`, and the
  // repetition written after it into `rep`: its operands are read into
  // `body` as the outer operands are, the delay before the group adding to
  // the group's leading delay, and its match items are attached at its end
  // (AttachGroupItems).
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

  // §16.9.2: whether the tokens ahead are a parenthesised group read into a
  // sequence of its own: one holding, at any depth, a token AtChainToken
  // answers true for and repeated after it by a consecutive count other than
  // the one number UnrollGroupRepetition copies the group's operands by, or,
  // Annex F.3.2 giving a repetition no clocked form, one writing a clocking
  // event at any depth and repeated at all, the elaborator holding that clock
  // to the one in force where the group stands. A malformed count is
  // answered as the group is read. The lexer is rewound.
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

  // §16.9.2: a group of more than one operand, or of a repeated one, repeated
  // by a range, `$`, a count of 0 or a count written as an expression, which
  // no number of copies of its operands spliced into the chain stands for, or
  // a repeated group writing a clocking event (AheadIsGroupReadWhole). It
  // is read into a sequence of its own standing as one operand, as
  // ParseNestedGroup reads one, the repetition on that operand for the
  // sequence monitor to iterate, and the group's match items on the
  // sequence's end, run at the end of each iteration (§16.10).
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
  // chain's end. Where that delay is one tick count, the interval begins
  // `lead` ticks before the first operand's least delay, seq's own leading
  // delay being any of §16.7's. Where it is a range, each tick of it begins
  // an interval of its own, so a 1 is read at its end, the interval
  // beginning at the tick the 1 is read at, and seq is read after the 1.
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

  // §16.13.1: `@(event_list)` or, §9.4 Syntax 9-4, `@name` before an
  // operand, the clock the operands from it on are evaluated on; answers
  // false where the event is malformed, and leaves `clock` as it was where
  // none is written.
  static bool ParseOperandClock(Parser& p, std::vector<EventExpr>& clock) {
    // §16.13.3: of two clocking events juxtaposed the second nullifies the
    // first, so the last written is the one in force.
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
      next.written = true;
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
      // §16.13.1: a clock the chain writes is kept on its operands, for the
      // elaborator to hold to the clock in force (Annex F.2).
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
    if (!ParserPropertySpecHelpers::ParseSequenceMatchItems(
            p, body.first_match_items))
      return false;
    return p.Match(TokenKind::kRParen);
  }
};

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

// §16.13.6/§9.4.4: trial-parse the simple clocked linear body
// `@(edge clk) b0 ##1 b1 ##1 ... bn` and record the clock + operands so the
// simulator can fire the sequence endpoint on a match. Diagnostics are
// suppressed and the lexer is rewound, so the harvest scan in
// ParseSequenceDecl re-reads the same tokens unchanged; any other body shape
// leaves the operands empty and no monitor is created, the leading clock
// kept all the same.
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
  // §9.4 Syntax 9-4: the clock is `@(event_expression)` or `@` and a name.
  if (ok && Match(TokenKind::kAt)) {
    if (Match(TokenKind::kLParen)) {
      clock = ParseEventList();
      ok = Match(TokenKind::kRParen);
    } else {
      clock.push_back(ParseNamedClockingEvent());
    }
  }
  // §16.16 (f): the clocking event the body opens with is the sequence's own
  // leading clocking event, the one an assertion instantiating the sequence
  // resolves to, whatever sequence_expr follows it; §16.7's grammar admits
  // shapes the linear form does not hold, a ranged repetition of a
  // parenthesised group, say, so the clock read whole is kept where the
  // operands are not.
  bool clock_read = ok;
  if (ok) ok = ParserSeqLinearHelpers::ParseLinearSeqOperands(*this, item);
  // The sequence_expr is terminated by ';' before `endsequence`.
  if (ok) Match(TokenKind::kSemicolon);
  ok = ok && Check(TokenKind::kKwEndsequence) &&
       !item->seq_linear.operands.empty();
  in_sequence_body_ = false;
  diag_.PopSuppress();
  lexer_.RestorePos(saved);
  if (clock_read) item->seq_clock = std::move(clock);
  if (!ok) item->seq_linear = SeqLinearBody{};
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
  // §16.9.8: `first_match ( sequence_expr [, match_items] )` is a term of its
  // own, the antecedent of an implication among them.
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
