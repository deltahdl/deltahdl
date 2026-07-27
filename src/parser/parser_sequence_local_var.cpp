#include "parser/parser.h"
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

}  // namespace

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
    diag_.Error(range_loc,
                "cycle-delay range bounds cannot be negative (§16.7)");
    return;
  }
  // §16.7 S6: the upper bound must be at least the lower bound.
  if (hi_mag < lo_mag) {
    diag_.Error(range_loc,
                "cycle-delay range upper bound must be at least the lower "
                "bound (§16.7)");
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
                "value (§16.7)");
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
    diag_.Error(range_loc, "cycle-delay value must be an integer (§16.7)");
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
  int depth = 1;
  bool expect_formal_name = true;

  bool item_saw_local = false;
  // §16.8.2 distinguishes "local was set by a keyword in this port item"
  // from "local was carried over via the inheritance rule." Only the
  // explicit-here case triggers the explicit-type-required check.
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

  void FinalizePortItem(DiagEngine& diag, ModuleItem* item) {
    if (!item_saw_local) return;
    if (item_local_explicit_here && !item_saw_explicit_type) {
      diag.Error(item_start,
                 "a local variable formal argument requires an explicit "
                 "type in its own port item (§16.8.2)");
    }
    if (item_saw_eq &&
        (item_dir == Direction::kInout || item_dir == Direction::kOutput)) {
      diag.Error(item_start,
                 "default actual argument is illegal for a local "
                 "variable formal argument of direction inout or "
                 "output (§16.8.2)");
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
                 "sequence port direction requires the 'local' keyword "
                 "(§16.8.2)");
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
    while (LexerCheck(lexer, TokenKind::kIdentifier)) {
      name_tok = lexer.Next();
      item_saw_explicit_type = true;
    }
    item->prop_formals.push_back(name_tok.text);
    // §16.8: the formal starts out with no default; a following `= actual`
    // (handled in DispatchTopLevel) flips this entry to true.
    item->prop_formal_has_default.push_back(false);
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
  }

  // §16.14.7: a system function that opens the current formal's default value
  // (it directly follows `=`). $inferred_clock may only default an untyped or
  // event formal; a formal that supplied an explicit data type is neither, so
  // that default is rejected (`event`, not a data type here, leaves
  // item_saw_explicit_type false and is correctly accepted). An inferred
  // clocking or disable function shall also be the entire default value
  // expression: a following token that is neither the formal separator ',' nor
  // the closing ')' means it is only part of a larger expression.
  void HandleSystemDefaultValue(Lexer& lexer, DiagEngine& diag) {
    auto fn = lexer.Peek().text;
    auto fn_loc = lexer.Peek().loc;
    bool is_inferred = fn == "$inferred_clock" || fn == "$inferred_disable";
    if (fn == "$inferred_clock" && item_saw_explicit_type) {
      diag.Error(fn_loc,
                 "$inferred_clock default requires an untyped or event "
                 "formal argument");
    }
    lexer.Next();
    if (is_inferred && !LexerCheck(lexer, TokenKind::kComma) &&
        !LexerCheck(lexer, TokenKind::kRParen)) {
      diag.Error(fn_loc,
                 "an inferred clocking or disable function must be the "
                 "entire default value of a formal argument");
    }
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
    } else if (IsBuiltinTypeKwForLocalVar(lexer.Peek().kind)) {
      lexer.Next();
      item_saw_explicit_type = true;
    } else if (item_saw_local &&
               IsDisallowedLocalVarTypeKw(lexer.Peek().kind)) {
      // §16.8.2: a local variable formal argument's type must be one of the
      // §16.6 data types; `sequence`/`event`/`property`/`untyped` are not, so
      // this is the disallowed-type error, not the missing-type error. Mark the
      // type as seen so FinalizePortItem does not also flag a missing type.
      diag.Error(lexer.Peek().loc,
                 "the type of a local variable formal argument must be one of "
                 "the types allowed in §16.6");
      item_saw_explicit_type = true;
      lexer.Next();
    } else if (LexerCheck(lexer, TokenKind::kEq)) {
      HandleDefaultEq(lexer, item);
    } else if (prev_kind == TokenKind::kEq &&
               LexerCheck(lexer, TokenKind::kSystemIdentifier)) {
      HandleSystemDefaultValue(lexer, diag);
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
static void ParseSequencePortList(Lexer& lexer, DiagEngine& diag,
                                  ModuleItem* item) {
  SequencePortScan scan;
  scan.item_start = lexer.Peek().loc;
  while (scan.depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (!scan.Step(lexer, diag, item)) break;
  }
}

// §16.13.6: parse the operand chain `b0 ##1 b1 ##1 ... bn` of a simple linear
// sequence body. Returns false on any non-unit cycle delay or parse failure;
// only `##1` between Boolean operands is supported by the linear monitor.
bool Parser::ParseLinearSeqOperands(std::vector<Expr*>& operands) {
  while (!Check(TokenKind::kKwEndsequence) && !Check(TokenKind::kSemicolon) &&
         !AtEnd()) {
    Expr* op = ParseExpr();
    if (!op) return false;
    operands.push_back(op);
    if (!Check(TokenKind::kHashHash)) break;
    Consume();  // '##'
    if (!Check(TokenKind::kIntLiteral) || CurrentToken().text != "1")
      return false;
    Consume();  // '1'
  }
  return true;
}

// §16.13.6/§9.4.4: trial-parse the simple clocked linear body
// `@(edge clk) b0 ##1 b1 ##1 ... bn` and record the clock + operands so the
// simulator can fire the sequence endpoint on a match. Diagnostics are
// suppressed and the lexer is rewound, so the harvest scan in ParseSequenceDecl
// re-reads the same tokens unchanged; any other body shape leaves the fields
// empty and no monitor is created.
void Parser::CaptureLinearSequenceBody(ModuleItem* item) {
  if (!Check(TokenKind::kAt)) return;
  auto saved = lexer_.SavePos();
  diag_.PushSuppress();
  Consume();  // '@'
  std::vector<EventExpr> clock;
  bool ok = Match(TokenKind::kLParen);
  if (ok) {
    clock = ParseEventList();
    ok = Match(TokenKind::kRParen);
  }
  std::vector<Expr*> operands;
  if (ok) ok = ParseLinearSeqOperands(operands);
  // The sequence_expr is terminated by ';' before `endsequence`.
  if (ok) Match(TokenKind::kSemicolon);
  ok = ok && Check(TokenKind::kKwEndsequence) && !operands.empty();
  diag_.PopSuppress();
  lexer_.RestorePos(saved);
  if (ok) {
    item->seq_clock = std::move(clock);
    item->seq_linear_operands = std::move(operands);
  }
}

ModuleItem* Parser::ParseSequenceDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kSequenceDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwSequence);
  item->name = Expect(TokenKind::kIdentifier).text;

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
    ParseSequencePortList(lexer_, diag_, item);
  }

  Expect(TokenKind::kSemicolon);

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
  Expect(TokenKind::kKwEndsequence);
  MatchEndLabel(item->name);
  return item;
}

// §16.10: a local variable declared in the sequence body cannot be used in the
// body's clocking event expression. The assertion_variable_declarations are
// harvested before this runs, so any identifier inside a `@( ... )` event group
// (an edge signal or an iff guard) that matches a body local is rejected. The
// whole parenthesized event group is consumed so its names are not also
// recorded as sequence instance references.
void Parser::ScanSequenceClockEvent(ModuleItem* item) {
  // §16.16(b2): count each explicit clocking event so a multiclocked sequence
  // (a non-leading or additional `@(...)`) can be recognized.
  ++item->decl_clock_event_count;
  Consume();  // '@'
  if (!Check(TokenKind::kLParen)) return;
  Consume();  // '('
  int depth = 1;
  while (depth > 0 && !AtEnd()) {
    if (Check(TokenKind::kLParen)) {
      ++depth;
    } else if (Check(TokenKind::kRParen)) {
      --depth;
    } else if (Check(TokenKind::kIdentifier)) {
      RejectLocalInClockEvent(item, CurrentToken().text);
    }
    Consume();
  }
}

void Parser::RejectLocalInClockEvent(const ModuleItem* item,
                                     std::string_view name) {
  for (auto local : item->prop_seq_assert_vars) {
    if (local == name) {
      diag_.Error(CurrentLoc(), "local variable \"" + std::string(name) +
                                    "\" may not be used in a clocking event "
                                    "expression (§16.10)");
      return;
    }
  }
}

// §16.10: assertion_variable_declarations precede the sequence_expr in the
// body, so they are harvested while still at the head of the body; once a token
// appears that does not start a declaration the scan falls through to the
// sequence_instance reference scan the §16.8 cycle rule needs.
void Parser::ScanSequenceBody(ModuleItem* item) {
  bool in_decl_prefix = true;
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
      item->prop_instance_refs.push_back(Consume().text);
      continue;
    }
    Consume();
  }
}

}  // namespace delta
