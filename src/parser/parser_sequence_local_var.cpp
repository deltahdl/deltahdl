#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"
#include "parser/parser_sequence_property_decl_internal.h"

namespace delta {

namespace {

// §16.7: parse a plain decimal token like "5" into its integer value. Sized
// or based literals ("5'd10", "3'b101") return false; the caller leaves
// validation to downstream stages that have full constant-folding.
bool TryParsePlainDecimal(std::string_view text, uint64_t& out) {
  if (text.empty()) return false;
  uint64_t v = 0;
  for (char c : text) {
    if (c < '0' || c > '9') return false;
    if (v > (UINT64_MAX - 9) / 10) return false;
    v = v * 10 + static_cast<uint64_t>(c - '0');
  }
  out = v;
  return true;
}

bool IsEventFormalOf(const ModuleItem* item, std::string_view name) {
  for (size_t i = 0; i < item->prop_formals.size(); ++i) {
    if (item->prop_formals[i] == name) {
      return item->prop_formal_type_kw[i] == TokenKind::kKwEvent;
    }
  }
  return false;
}

// §16.8: an identifier written as the whole actual of an instance is bound to
// the instantiated declaration's formal, so what may be written there is what
// that formal admits, an event_expression where it is typed `event`.
bool IsWholeInstanceActual(const ModuleItem* item, SourceLoc loc) {
  for (const auto& arg : item->assertion_instance_args) {
    if (arg.loc.file_id == loc.file_id && arg.loc.line == loc.line &&
        arg.loc.column == loc.column) {
      return true;
    }
  }
  return false;
}

// §16.8.1 rule b): a formal of type `event` is referenced only where an
// event_expression may be written. The clocking events are consumed before the
// sequence body scan reaches an identifier, so a reference to one read there
// stands in the sequence_expr; one after `.` or `::` names a member instead.
void ReportEventFormalReference(DiagEngine& diag, const ModuleItem* item,
                                const Token& tok, bool after_select) {
  if (after_select || !IsEventFormalOf(item, tok.text) ||
      IsWholeInstanceActual(item, tok.loc)) {
    return;
  }
  diag.Error(tok.loc,
             "formal argument '" + std::string(tok.text) +
                 "' of type event is referenced where no event expression may "
                 "be written",
             Subclause("16.8.1"));
}

}  // namespace

// §16.8.2: the type of a local variable formal argument shall be one of the
// types allowed in §16.6. The formal-type categories that §16.8.1 permits for
// an ordinary (non-local) formal — `sequence`, `event`, `property`, and the
// keyword `untyped` — are not among the §16.6 data types, so specifying one of
// them as the type of a `local` formal is illegal (the illegal example in
// §16.8.2 rejects `local event e` on exactly these grounds). These keywords are
// recognised head-on so the diagnostic names the real problem (a disallowed
// type) rather than being mistaken for a missing type.
void ReportChandleFormal(DiagEngine& diag, const Token& type_tok) {
  if (type_tok.kind != TokenKind::kKwChandle) return;
  diag.Error(type_tok.loc,
             "a sequence or property formal argument may not be of type "
             "chandle",
             Subclause("16.8"));
}

bool IsDisallowedLocalVarTypeKw(TokenKind k) {
  switch (k) {
    case TokenKind::kKwEvent:
    case TokenKind::kKwSequence:
    case TokenKind::kKwProperty:
    case TokenKind::kKwUntyped:
      return true;
    default:
      return false;
  }
}

void Parser::ValidateLiteralCycleDelayRange(SourceLoc range_loc) {
  // §16.7: only the literal `##[ [-]INTLIT : [-]INTLIT ]` form is checked
  // here. Symbolic bounds need full constant evaluation and are deferred to
  // later stages. The five-to-seven token window is peeked under SavePos so
  // the body loop still sees every token afterwards.
  if (!Check(TokenKind::kLBracket)) return;
  auto saved = lexer_.SavePos();
  Consume();  // [
  bool lo_negative = false;
  if (Check(TokenKind::kMinus)) {
    lo_negative = true;
    Consume();
  }
  if (!Check(TokenKind::kIntLiteral)) {
    lexer_.RestorePos(saved);
    return;
  }
  Token lo = Consume();
  if (!Check(TokenKind::kColon)) {
    lexer_.RestorePos(saved);
    return;
  }
  Consume();  // :
  bool hi_negative = false;
  if (Check(TokenKind::kMinus)) {
    hi_negative = true;
    Consume();
  }
  if (!Check(TokenKind::kIntLiteral)) {
    lexer_.RestorePos(saved);
    return;
  }
  Token hi = Consume();
  if (!Check(TokenKind::kRBracket)) {
    lexer_.RestorePos(saved);
    return;
  }
  lexer_.RestorePos(saved);

  uint64_t lo_mag = 0;
  uint64_t hi_mag = 0;
  if (!TryParsePlainDecimal(lo.text, lo_mag)) return;
  if (!TryParsePlainDecimal(hi.text, hi_mag)) return;

  // §16.7 S2: a literal lower or upper bound below zero is illegal.
  if (lo_negative || hi_negative) {
    diag_.Error(range_loc, "cycle-delay range bounds cannot be negative",
                Subclause("16.7"));
    return;
  }
  // §16.7 S6: the upper bound must be at least the lower bound.
  if (hi_mag < lo_mag) {
    diag_.Error(range_loc,
                "cycle-delay range upper bound must be at least the lower "
                "bound",
                Subclause("16.7"));
  }
}

// Advance the bracket-nesting and conditional-depth counters over one token of
// a parenthesized constant_primary, marking `is_min_typ_max` when a top-level
// ':' appears that is not the ':' of a `?:` conditional.
static void ScanMinTypMaxToken(TokenKind k, int& nesting, int& cond_depth,
                               bool& is_min_typ_max) {
  if (k == TokenKind::kLParen || k == TokenKind::kLBracket ||
      k == TokenKind::kLBrace) {
    ++nesting;
    return;
  }
  if (k == TokenKind::kRParen || k == TokenKind::kRBracket ||
      k == TokenKind::kRBrace) {
    --nesting;
    return;
  }
  if (nesting != 1) return;
  if (k == TokenKind::kQuestion) {
    ++cond_depth;
    return;
  }
  if (k != TokenKind::kColon) return;
  if (cond_depth > 0) {
    --cond_depth;  // the ':' of a conditional, not a min:typ:max separator.
  } else {
    is_min_typ_max = true;
  }
}

void Parser::ValidateCycleDelayMinTypMax(SourceLoc range_loc) {
  // §16.7: inside a cycle_delay_range, it is illegal for the constant_primary
  // to be a constant_mintypmax_expression (a `min:typ:max` triple) that is not
  // also a plain constant_expression. The triple always takes the parenthesized
  // `( a : b : c )` shape, so a top-level ':' inside the leading parentheses
  // that is not the ':' of a `?:` conditional marks the illegal form. A plain
  // `( expr )` or a `( sel ? a : b )` conditional stays legal. Tokens are
  // peeked under SavePos/RestorePos so the body harvest loop still sees them.
  if (!Check(TokenKind::kLParen)) return;
  auto saved = lexer_.SavePos();
  Consume();           // '('
  int nesting = 1;     // open ( [ { — the leading '(' is the first level.
  int cond_depth = 0;  // '?' tokens still awaiting their matching ':'.
  bool is_min_typ_max = false;
  while (nesting > 0 && !Check(TokenKind::kEof)) {
    ScanMinTypMaxToken(CurrentToken().kind, nesting, cond_depth,
                       is_min_typ_max);
    Consume();
  }
  lexer_.RestorePos(saved);
  if (is_min_typ_max) {
    diag_.Error(range_loc,
                "a min:typ:max expression may not be used as a cycle-delay "
                "value",
                Subclause("16.7"));
  }
}

void Parser::ValidateCycleDelayIntegerValue(SourceLoc range_loc) {
  // §16.7: the constant_primary of a `## delay` is a constant_expression that
  // shall result in an integer value. A real or string literal in that position
  // can never yield an integer, so it is rejected here. This peeks the current
  // token only (no Consume), so the body harvest loop still sees it afterwards.
  // The bracketed-range and parenthesized-primary forms are handled by the
  // sibling checks; this fires only on the bare `## <literal>` shape.
  if (Check(TokenKind::kRealLiteral) || Check(TokenKind::kStringLiteral)) {
    diag_.Error(range_loc, "cycle-delay value must be an integer",
                Subclause("16.7"));
  }
}

// Consumes the var_data_type prefix of an assertion_variable_declaration: the
// leading type keyword followed by any signing token and packed dimensions.
static void SkipAssertVarTypePrefix(Lexer& lexer) {
  lexer.Next();  // var_data_type's leading type keyword.
  while (LexerCheck(lexer, TokenKind::kKwSigned) ||
         LexerCheck(lexer, TokenKind::kKwUnsigned)) {
    lexer.Next();
  }
  while (LexerCheck(lexer, TokenKind::kLBracket)) {
    int b_depth = 1;
    lexer.Next();
    while (b_depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
      if (LexerCheck(lexer, TokenKind::kLBracket))
        ++b_depth;
      else if (LexerCheck(lexer, TokenKind::kRBracket))
        --b_depth;
      lexer.Next();
    }
  }
}

// Skips the initializer expression of one variable_decl_assignment, stopping at
// the top-level comma or semicolon that terminates it (or at an unbalanced
// closing bracket). The '=' has already been consumed by the caller.
static void SkipAssertVarInitExpr(Lexer& lexer) {
  int e_depth = 0;
  while (!lexer.Peek().Is(TokenKind::kEof)) {
    if (LexerCheck(lexer, TokenKind::kLParen) ||
        LexerCheck(lexer, TokenKind::kLBracket) ||
        LexerCheck(lexer, TokenKind::kLBrace)) {
      ++e_depth;
      lexer.Next();
    } else if (LexerCheck(lexer, TokenKind::kRParen) ||
               LexerCheck(lexer, TokenKind::kRBracket) ||
               LexerCheck(lexer, TokenKind::kRBrace)) {
      if (e_depth == 0) break;
      --e_depth;
      lexer.Next();
    } else if (e_depth == 0 && (LexerCheck(lexer, TokenKind::kComma) ||
                                LexerCheck(lexer, TokenKind::kSemicolon))) {
      break;
    } else {
      lexer.Next();
    }
  }
}

void Parser::HarvestAssertionVariableDecl(ModuleItem* item) {
  // §16.10 Syntax 16-13: assertion_variable_declaration ::= var_data_type
  // list_of_variable_decl_assignments ; — consume the data-type prefix
  // (one keyword plus any packed dimensions or signing token) and then walk
  // the comma-separated list of <identifier> [ = <expression> ] entries
  // until the closing semicolon. Each identifier names a distinct local
  // variable in the sequence/property body.
  // §16.10 with §16.6: chandle is not among the types a local variable may
  // be declared with.
  if (Check(TokenKind::kKwChandle)) {
    diag_.Error(CurrentLoc(),
                "an assertion variable may not be declared of type chandle",
                Subclause("16.10"));
  }
  SkipAssertVarTypePrefix(lexer_);
  while (!Check(TokenKind::kSemicolon) && !AtEnd()) {
    if (Check(TokenKind::kIdentifier)) {
      auto tok = Consume();
      item->prop_seq_assert_vars.push_back(tok.text);
      if (Check(TokenKind::kEq)) {
        Consume();
        SkipAssertVarInitExpr(lexer_);
      }
      if (Check(TokenKind::kComma)) Consume();
    } else {
      Consume();
    }
  }
  if (Check(TokenKind::kSemicolon)) Consume();
}

// §16.8 sequence_port_list scan state carried across loop iterations. Groups
// the parenthesis depth, the per-port-item §16.8.2 local-variable trackers,
// and the formal-name expectation so each iteration's handler can update them
// in place.
struct SequencePortScan {
  // The parser whose lexer the scan reads, which parses a formal's default.
  Parser* parser = nullptr;
  int depth = 1;
  bool expect_formal_name = true;

  bool item_saw_local = false;
  // §16.8.2 tells a formal whose own port item writes `local` apart from one
  // that takes `local` over from the formal before it. Only the first
  // triggers the explicit-type-required check.
  bool item_local_explicit_here = false;
  // §16.8.2: a local formal must have its type specified explicitly in
  // the same port item. We mark `explicit type seen` when we consume a
  // built-in type keyword or when the formal-name harvest finds more than
  // one identifier in the chain (the first is a type alias).
  bool item_saw_explicit_type = false;
  Direction item_dir = Direction::kInput;
  bool item_saw_eq = false;
  SourceLoc item_start;
  // §16.14.7: kind of the previously consumed port-list token, used to detect
  // the head of a formal's default value (the token immediately after `=`) so a
  // $inferred_clock default on a typed formal can be rejected.
  TokenKind prev_kind = TokenKind::kComma;
  // §16.8.1: the type keyword in force for the formals that follow, kEof for
  // untyped, cleared by `untyped` and by a type the keyword alone does not
  // name, which a `[` or a type identifier after it shows.
  TokenKind carry_type_kw = TokenKind::kEof;
  // §16.14.7: whether the type in force for the formals that follow admits a
  // $inferred_clock default, which only an untyped or `event` formal does. A
  // data type, written or carried from an earlier formal (§16.8), or
  // `sequence`, does not.
  bool clock_default_allowed = true;

  void FinalizePortItem(DiagEngine& diag, ModuleItem* item) {
    if (!item_saw_local) return;
    if (item_local_explicit_here && !item_saw_explicit_type) {
      diag.Error(item_start,
                 "a local variable formal argument requires an explicit "
                 "type in its own port item",
                 Subclause("16.8.2"));
    }
    if (item_saw_eq &&
        (item_dir == Direction::kInout || item_dir == Direction::kOutput)) {
      diag.Error(item_start,
                 "default actual argument is illegal for a local "
                 "variable formal argument of direction inout or "
                 "output",
                 Subclause("16.8.2"));
    }
    item->prop_seq_local_lvar_directions.push_back(item_dir);
  }

  // §16.8.2 carry-through: a port item that supplies only an identifier
  // inherits the `local` designation, direction, and type of the nearest
  // preceding port item that declared them explicitly. A port item that
  // begins with `local`, a direction keyword, or a built-in type keyword
  // is a fresh starter and breaks the carry.
  void ResetAfterComma(Lexer& lexer) {
    bool next_is_fresh_starter = LexerCheck(lexer, TokenKind::kKwLocal) ||
                                 LexerCheck(lexer, TokenKind::kKwInput) ||
                                 LexerCheck(lexer, TokenKind::kKwOutput) ||
                                 LexerCheck(lexer, TokenKind::kKwInout) ||
                                 IsBuiltinTypeKwForLocalVar(lexer.Peek().kind);
    if (next_is_fresh_starter) {
      item_saw_local = false;
      item_dir = Direction::kInput;
    }
    // Else: carry item_saw_local and item_dir from the previous port item.
    // Per-port-item flags never carry: a carried port item neither sees
    // `local` explicitly here nor declares its own type.
    item_local_explicit_here = false;
    item_saw_explicit_type = false;
    item_saw_eq = false;
    expect_formal_name = true;
  }

  // §16.8.2 direction keyword: records the direction and polices the
  // requirement that a direction be preceded by `local`.
  void HandleDirection(Lexer& lexer, DiagEngine& diag) {
    auto dir_tok = lexer.Next();
    if (!item_saw_local) {
      diag.Error(dir_tok.loc,
                 "sequence port direction requires the 'local' keyword",
                 Subclause("16.8.2"));
    }
    if (dir_tok.kind == TokenKind::kKwInput) {
      item_dir = Direction::kInput;
    } else if (dir_tok.kind == TokenKind::kKwOutput) {
      item_dir = Direction::kOutput;
    } else {
      item_dir = Direction::kInout;
    }
  }

  // Harvests the formal_port_identifier (rightmost identifier of the chain).
  void HarvestFormalName(Lexer& lexer, ModuleItem* item) {
    auto name_tok = lexer.Next();
    // Walk past any subsequent identifiers/type tokens until we hit the
    // separator; the rightmost identifier is the formal_port_identifier.
    // §16.8.2: a chain of more than one identifier means the leading
    // identifier(s) supply a (user-defined) type alias, satisfying the
    // explicit-type requirement.
    bool user_typed = false;
    while (LexerCheck(lexer, TokenKind::kIdentifier)) {
      name_tok = lexer.Next();
      item_saw_explicit_type = true;
      user_typed = true;
    }
    if (user_typed) {
      carry_type_kw = TokenKind::kEof;
      clock_default_allowed = false;
    }
    item->prop_formals.push_back(name_tok.text);
    item->prop_formal_type_kw.push_back(carry_type_kw);
    // §16.8.2: whether this formal is a local variable formal argument, which
    // §16.10 keeps out of the sequence's clocking events.
    item->prop_formal_is_local.push_back(item_saw_local);
    // §16.8: the formal starts out with no default; a following `= actual`
    // (handled in DispatchTopLevel) flips this entry to true.
    item->prop_formal_has_default.push_back(false);
    item->prop_formal_defaults.push_back(nullptr);
    item->prop_formal_inferred.push_back(InferredDefault::kNone);
    expect_formal_name = false;
  }

  // depth==1 comma: finalize the closing port item, then prepare for the next.
  void HandleComma(Lexer& lexer, DiagEngine& diag, ModuleItem* item) {
    FinalizePortItem(diag, item);
    lexer.Next();
    item_start = lexer.Peek().loc;
    ResetAfterComma(lexer);
  }

  // depth==1 `local`: opens a local-formal port item declared explicitly here.
  void HandleLocal(Lexer& lexer) {
    if (!item_saw_local) item_start = lexer.Peek().loc;
    item_saw_local = true;
    item_local_explicit_here = true;
    lexer.Next();
  }

  // §16.8.1: a data type keyword types the formals after it until the next
  // type, and `event`, `sequence` and `untyped` do the same for a formal that
  // is not local, `untyped` ending a type's reach; a `[` after a data type
  // keyword makes a type the keyword alone does not name. Returns true where
  // the token was one of these and was consumed.
  bool HandleTypeKeyword(Lexer& lexer, DiagEngine& diag) {
    TokenKind kind = lexer.Peek().kind;
    if (IsBuiltinTypeKwForLocalVar(kind)) {
      ReportChandleFormal(diag, lexer.Next());
      carry_type_kw =
          LexerCheck(lexer, TokenKind::kLBracket) ? TokenKind::kEof : kind;
      item_saw_explicit_type = true;
      clock_default_allowed = false;
      return true;
    }
    if (item_saw_local || !IsDisallowedLocalVarTypeKw(kind)) return false;
    lexer.Next();
    carry_type_kw = kind == TokenKind::kKwUntyped ? TokenKind::kEof : kind;
    clock_default_allowed =
        kind == TokenKind::kKwUntyped || kind == TokenKind::kKwEvent;
    return true;
  }

  // Handles the depth==1 (top-level) tokens of a port item. Returns true if the
  // current token was consumed here; false means the caller falls through to
  // the default skip. All branches assume depth==1 has already been
  // established.
  // §16.8: `formal = default_expression` gives the most recently harvested
  // formal a default actual argument.
  void HandleDefaultEq(Lexer& lexer, ModuleItem* item) {
    item_saw_eq = true;
    if (!item->prop_formal_has_default.empty()) {
      item->prop_formal_has_default.back() = true;
    }
    lexer.Next();
    expect_formal_name = false;
    RecordDefault(item);
  }

  // §16.8: the default actual itself, kept beside the formal for an instance
  // that omits the formal to take.
  void RecordDefault(ModuleItem* item) {
    if (parser == nullptr || item->prop_formal_defaults.empty()) return;
    item->prop_formal_defaults.back() =
        ParserPropertySpecHelpers::ParseFormalDefault(*parser);
  }

  bool DispatchTopLevel(Lexer& lexer, DiagEngine& diag, ModuleItem* item) {
    if (LexerCheck(lexer, TokenKind::kComma)) {
      HandleComma(lexer, diag, item);
    } else if (LexerCheck(lexer, TokenKind::kKwLocal)) {
      HandleLocal(lexer);
    } else if (LexerCheck(lexer, TokenKind::kKwInput) ||
               LexerCheck(lexer, TokenKind::kKwOutput) ||
               LexerCheck(lexer, TokenKind::kKwInout)) {
      HandleDirection(lexer, diag);
    } else if (HandleTypeKeyword(lexer, diag)) {
      // The keyword was consumed and its type recorded for the formals after.
    } else if (item_saw_local &&
               IsDisallowedLocalVarTypeKw(lexer.Peek().kind)) {
      // §16.8.2: a local variable formal argument's type must be one of the
      // §16.6 data types; `sequence`/`event`/`property`/`untyped` are not, so
      // this is the disallowed-type error, not the missing-type error. Mark the
      // type as seen so FinalizePortItem does not also flag a missing type.
      diag.Error(lexer.Peek().loc,
                 "the type of a local variable formal argument must be one of "
                 "the types allowed in §16.6",
                 Subclause("16.8.2"));
      item_saw_explicit_type = true;
      lexer.Next();
    } else if (LexerCheck(lexer, TokenKind::kEq)) {
      HandleDefaultEq(lexer, item);
    } else if (prev_kind == TokenKind::kEq &&
               LexerCheck(lexer, TokenKind::kSystemIdentifier)) {
      ScanSystemDefaultValue(lexer, diag, item, clock_default_allowed);
    } else if (expect_formal_name &&
               LexerCheck(lexer, TokenKind::kIdentifier)) {
      HarvestFormalName(lexer, item);
    } else {
      return false;
    }
    return true;
  }

  // Consumes one token of the port list, tracking the previous token kind so
  // DispatchTopLevel can recognize a default-value head. Returns false once the
  // matching ')' for the opening '(' has been consumed (list complete).
  bool Step(Lexer& lexer, DiagEngine& diag, ModuleItem* item) {
    TokenKind this_kind = lexer.Peek().kind;
    bool keep_going = StepDispatch(lexer, diag, item);
    prev_kind = this_kind;
    return keep_going;
  }

  bool StepDispatch(Lexer& lexer, DiagEngine& diag, ModuleItem* item) {
    if (LexerCheck(lexer, TokenKind::kLParen)) {
      lexer.Next();
      ++depth;
      return true;
    }
    if (LexerCheck(lexer, TokenKind::kRParen)) {
      if (depth == 1) FinalizePortItem(diag, item);
      lexer.Next();
      --depth;
      return depth != 0;
    }
    if (depth == 1 && DispatchTopLevel(lexer, diag, item)) return true;
    lexer.Next();
    return true;
  }
};

// §16.8 sequence_port_list. On entry the opening '(' has already been consumed;
// drains the comma-separated formal list through its matching ')', harvesting
// formal_port_identifier names and policing the §16.8.2 local-variable rules.
// Behaviour matches the original inline loop exactly.
static void ParseSequencePortList(Parser& parser, Lexer& lexer,
                                  DiagEngine& diag, ModuleItem* item) {
  SequencePortScan scan;
  scan.parser = &parser;
  scan.item_start = lexer.Peek().loc;
  while (scan.depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (!scan.Step(lexer, diag, item)) break;
  }
}

ModuleItem* Parser::ParseSequenceDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kSequenceDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwSequence, Subclause("16.8"));
  item->name = Expect(TokenKind::kIdentifier, Subclause("16.8")).text;

  // §16.8 sequence_port_list: harvest formal_port_identifier names so the
  // elaborator can flatten instances and run cycle detection.
  //
  // §16.8.2 local variable formal arguments: a port item may begin with the
  // keyword `local`, optionally followed by one of the directions `input`,
  // `inout`, or `output`. Two well-formedness rules are checked here:
  //   (a) a direction without a preceding `local` is illegal in a sequence
  //       port list;
  //   (b) a default actual argument is illegal for a local formal of
  //       direction `inout` or `output`.
  // For each local-marked formal we also record its (possibly inferred)
  // direction so later stages can apply the §16.10 local-variable rules.
  if (Match(TokenKind::kLParen)) {
    ParseSequencePortList(*this, lexer_, diag_, item);
  }

  Expect(TokenKind::kSemicolon, Subclause("16.8"));
  ParserPropertySpecHelpers::RecordAssertionReads(*this, item,
                                                  TokenKind::kKwEndsequence);

  // §16.16(b1): a sequence_expr may open with an explicit leading clocking
  // event. Record its presence (the body's first token is `@`) so a clocking
  // block, which forbids such an event on the declarations it contains, can
  // reject it.
  item->decl_has_leading_clock = Check(TokenKind::kAt);

  // §16.13.6: capture the simple clocked linear body for the simulator's
  // sequence.triggered monitor. This is a trial parse that suppresses
  // diagnostics and rewinds, so the harvest scan below runs over the same
  // tokens unchanged.
  CaptureLinearSequenceBody(item);

  ScanSequenceBody(item);
  Expect(TokenKind::kKwEndsequence, Subclause("16.8"));
  MatchEndLabel(item->name);
  return item;
}

// §16.10: a local variable of the sequence, one its body declares or a local
// variable formal argument, cannot be used in the body's clocking event
// expression, which is the condition Annex F.5.1 puts on its clock rewrite.
// The assertion_variable_declarations are harvested before this runs, so any
// identifier inside a `@( ... )` event group (an edge signal or an iff guard)
// that matches one is rejected. The whole parenthesized event group is
// consumed so its names are not also recorded as sequence instance references.
void Parser::ScanSequenceClockEvent(ModuleItem* item) {
  // §16.16(b2): count each explicit clocking event so a multiclocked sequence
  // (a non-leading or additional `@(...)`) can be recognized.
  ++item->decl_clock_event_count;
  Consume();  // '@'
  // §16.16: `@name` writes the clocking event as one identifier, an
  // event_expression position as the parenthesized group is.
  if (Check(TokenKind::kIdentifier)) {
    item->prop_instance_refs.push_back(Consume().text);
    return;
  }
  ScanClockEventGroupForLocals(lexer_, diag_, item);
}

// §16.10: assertion_variable_declarations precede the sequence_expr in the
// body, so they are harvested while still at the head of the body; once a token
// appears that does not start a declaration the scan falls through to the
// sequence_instance reference scan the §16.8 cycle rule needs.
void Parser::ScanSequenceBody(ModuleItem* item) {
  bool in_decl_prefix = true;
  // Whether the token before stands for a member or a scope selection, `.` or
  // `::`, so an identifier after it names a member rather than a formal.
  bool after_select = false;
  while (!Check(TokenKind::kKwEndsequence) && !AtEnd()) {
    if (in_decl_prefix && IsBuiltinTypeKwForLocalVar(CurrentToken().kind)) {
      HarvestAssertionVariableDecl(item);
      continue;
    }
    in_decl_prefix = false;

    if (Check(TokenKind::kAt)) {
      ScanSequenceClockEvent(item);
      continue;
    }
    if (Check(TokenKind::kHashHash)) {
      auto delay_loc = CurrentLoc();
      Consume();
      ValidateLiteralCycleDelayRange(delay_loc);
      ValidateCycleDelayMinTypMax(delay_loc);
      ValidateCycleDelayIntegerValue(delay_loc);
      continue;
    }
    if (Check(TokenKind::kIdentifier)) {
      auto tok = Consume();
      ReportEventFormalReference(diag_, item, tok, after_select);
      after_select = false;
      item->prop_instance_refs.push_back(tok.text);
      continue;
    }
    after_select = Check(TokenKind::kDot) || Check(TokenKind::kColonColon);
    Consume();
  }
}

// §16.12 with §6.16: the data type a property formal is declared with,
// read where the parse stands on the keyword opening it, its signing and
// packed dimensions included, and kept for what reads the formal's type.
DataType* ParserPropertySpecHelpers::ParseFormalType(Parser& p) {
  return p.arena_.Create<DataType>(p.ParseDataType());
}

// §16.12 with §6.18: a formal declared with the user-defined type `name`.
DataType* ParserPropertySpecHelpers::NamedFormalType(Parser& p,
                                                     std::string_view name) {
  auto* type = p.arena_.Create<DataType>();
  type->kind = DataTypeKind::kNamed;
  type->type_name = name;
  return type;
}

}  // namespace delta
