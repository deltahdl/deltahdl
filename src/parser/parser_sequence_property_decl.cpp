#include "parser/parser.h"

namespace delta {

// Replicates Parser::Check directly against a Lexer so the free-function
// helpers in this file see the same identifier/escaped-identifier folding the
// member helpers use.
static bool LexerCheck(Lexer& lexer, TokenKind kind) {
  auto cur = lexer.Peek().kind;
  if (kind == TokenKind::kIdentifier) {
    return cur == TokenKind::kIdentifier ||
           cur == TokenKind::kEscapedIdentifier;
  }
  return cur == kind;
}

// §16.12.17 Restriction 4: cross-token state for the actual-argument scan of
// one property instance. `d` is the parenthesis depth; the per-argument fields
// accumulate the identifiers and token count of the argument currently being
// read so finalize() can classify it as a single-identifier actual.
struct InstanceArgScan {
  PropertyInstanceArgInfo info;
  int d = 1;
  std::vector<std::string_view> cur_idents;
  int cur_tokens = 0;
  bool arg_has_content = false;
  std::string_view prev_ident;
  bool prev_was_ident = false;

  void Finalize() {
    info.arg_idents.push_back(cur_idents);
    info.arg_is_single_ident.push_back(cur_tokens == 1 &&
                                       cur_idents.size() == 1);
    cur_idents.clear();
    cur_tokens = 0;
  }

  // Consumes one token of the argument list. Returns false once the matching
  // ')' for the opening '(' has been consumed (scan complete).
  bool Step(Lexer& lexer, ModuleItem* item) {
    if (LexerCheck(lexer, TokenKind::kLParen)) {
      if (prev_was_ident) item->prop_instance_refs.push_back(prev_ident);
      lexer.Next();
      ++d;
      ++cur_tokens;
      arg_has_content = true;
      prev_was_ident = false;
    } else if (LexerCheck(lexer, TokenKind::kRParen)) {
      lexer.Next();
      --d;
      if (d == 0) {
        if (arg_has_content) Finalize();
        return false;
      }
      ++cur_tokens;
      prev_was_ident = false;
    } else if (d == 1 && LexerCheck(lexer, TokenKind::kComma)) {
      lexer.Next();
      Finalize();
      arg_has_content = true;
      prev_was_ident = false;
    } else if (LexerCheck(lexer, TokenKind::kIdentifier)) {
      auto t = lexer.Next();
      cur_idents.push_back(t.text);
      ++cur_tokens;
      arg_has_content = true;
      prev_ident = t.text;
      prev_was_ident = true;
    } else {
      lexer.Next();
      ++cur_tokens;
      arg_has_content = true;
      prev_was_ident = false;
    }
    return true;
  }
};

// §16.12.17 Restriction 4: capture the actual-argument shape of one property
// instance. On entry the lexer's current token is the opening '(' of the
// argument list; on return the matching ')' has been consumed. Nested instance
// references found within the arguments are still recorded into
// prop_instance_refs so the dependency digraph is unaffected.
static void CaptureInstanceArgs(Lexer& lexer, ModuleItem* item,
                                std::string_view callee) {
  InstanceArgScan scan;
  scan.info.callee = callee;
  lexer.Next();  // '('
  while (scan.d > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (!scan.Step(lexer, item)) break;
  }
  item->prop_instance_args.push_back(std::move(scan.info));
}

// §16.6/§16.10: a built-in scalar/integral/string type keyword that may head
// the var_data_type of an assertion_variable_declaration. User-defined type
// aliases also satisfy the grammar, but the parser's best-effort harvest only
// needs to recognise the built-in cases.
static bool IsBuiltinTypeKwForLocalVar(TokenKind k) {
  switch (k) {
    case TokenKind::kKwReg:
    case TokenKind::kKwLogic:
    case TokenKind::kKwBit:
    case TokenKind::kKwByte:
    case TokenKind::kKwShortint:
    case TokenKind::kKwInt:
    case TokenKind::kKwLongint:
    case TokenKind::kKwInteger:
    case TokenKind::kKwReal:
    case TokenKind::kKwShortreal:
    case TokenKind::kKwRealtime:
    case TokenKind::kKwTime:
    case TokenKind::kKwString:
    case TokenKind::kKwChandle:
      return true;
    default:
      return false;
  }
}

// §16.12 named-property port-list scan state carried across loop iterations.
struct PropertyPortScan {
  int depth = 1;
  bool expect_formal_name = true;
  bool saw_local = false;
  // §16.12.19 / §16.12.17 Restriction 4: track whether the current formal was
  // declared as a local variable formal argument. `local` qualifies the whole
  // comma-separated run of names until a fresh type specifier (not directly
  // following `local`/`input`) begins a new, unqualified item.
  bool local_run = false;
  TokenKind prev_kind = TokenKind::kComma;

  // Handles the formal-name harvest branch (§16.12 formal_port_identifier).
  void HarvestFormalName(Lexer& lexer, ModuleItem* item) {
    auto name_tok = lexer.Next();
    if (!LexerCheck(lexer, TokenKind::kComma) &&
        !LexerCheck(lexer, TokenKind::kRParen) &&
        !LexerCheck(lexer, TokenKind::kEq)) {
      if (LexerCheck(lexer, TokenKind::kIdentifier)) {
        name_tok = lexer.Next();
      }
    }
    item->prop_formals.push_back(name_tok.text);
    item->prop_formal_is_local.push_back(local_run);
    expect_formal_name = false;
    saw_local = false;
  }

  // Consumes one token of the port list. Returns false once the matching ')'
  // for the opening '(' has been consumed (list complete).
  bool Step(Lexer& lexer, DiagEngine& diag, ModuleItem* item) {
    TokenKind this_kind = lexer.Peek().kind;
    bool keep_going = true;
    if (LexerCheck(lexer, TokenKind::kLParen)) {
      lexer.Next();
      ++depth;
    } else if (LexerCheck(lexer, TokenKind::kRParen)) {
      lexer.Next();
      --depth;
      if (depth == 0) keep_going = false;
    } else if (depth == 1 && LexerCheck(lexer, TokenKind::kComma)) {
      lexer.Next();
      expect_formal_name = true;
      saw_local = false;
    } else if (depth == 1 && LexerCheck(lexer, TokenKind::kEq)) {
      lexer.Next();
      expect_formal_name = false;
    } else if (depth == 1 && LexerCheck(lexer, TokenKind::kKwLocal)) {
      lexer.Next();
      saw_local = true;
      local_run = true;
    } else if (depth == 1 && IsBuiltinTypeKwForLocalVar(lexer.Peek().kind)) {
      // A built-in type keyword that does not directly follow `local` or
      // `input` starts a fresh formal item whose qualifiers do not include
      // `local`, so the local-variable run ends here.
      if (prev_kind != TokenKind::kKwLocal &&
          prev_kind != TokenKind::kKwInput) {
        local_run = false;
      }
      lexer.Next();
    } else if (depth == 1 && (LexerCheck(lexer, TokenKind::kKwOutput) ||
                              LexerCheck(lexer, TokenKind::kKwInout))) {
      // §16.12.19: a local variable formal argument of a named property
      // shall have direction `input`; declaring one with direction `inout`
      // or `output` is illegal. The borrowed A.2.10 production
      // property_lvar_port_direction admits only `input`, so `output` and
      // `inout` have no legal role inside a property port, with or without a
      // preceding `local`.
      diag.Error(lexer.Peek().loc, "property port direction must be 'input'");
      lexer.Next();
      saw_local = false;
    } else if (depth == 1 && LexerCheck(lexer, TokenKind::kKwInput)) {
      // `input` is permitted only after `local`.
      if (!saw_local) {
        diag.Error(lexer.Peek().loc,
                   "property port direction 'input' requires 'local'");
      }
      lexer.Next();
      saw_local = false;
    } else if (expect_formal_name && depth == 1 &&
               LexerCheck(lexer, TokenKind::kIdentifier)) {
      HarvestFormalName(lexer, item);
    } else {
      lexer.Next();
    }
    prev_kind = this_kind;
    return keep_going;
  }
};

// §16.12 named-property port list. On entry the opening '(' has already been
// consumed; this drains the comma-separated formal list through its matching
// ')' , recording formal names and their local-variable qualification while
// policing the §16.12.19 direction rules. Behaviour matches the original
// inline loop exactly.
static void ParsePropertyPortList(Lexer& lexer, DiagEngine& diag,
                                  ModuleItem* item) {
  PropertyPortScan scan;
  while (scan.depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (!scan.Step(lexer, diag, item)) break;
  }
}

// §16.12 named-property body scan state carried across loop iterations. Groups
// the §16.12.16 case-default stack and the §16.12.17 negation/time-advance
// trackers as a single entity so cross-iteration state is preserved exactly as
// in the original inline loop.
struct PropertyBodyScanState {
  // §16.12.16: per open case statement, the count of default items seen.
  std::vector<int> case_default_counts;
  // §16.12.17 Restriction 1: the next instance reached is a negation operand.
  bool expect_negated_operand = false;
  // §16.12.17 Restriction 3: a time-advancing operator has been seen.
  bool saw_time_advance = false;
};

// §16.12.16: handles the `case`/`endcase`/`default` family that maintains the
// per-property-case default-item stack. Returns true if the current token was
// consumed here.
static bool ScanCaseDefaultToken(Lexer& lexer, DiagEngine& diag,
                                 PropertyBodyScanState& state) {
  if (LexerCheck(lexer, TokenKind::kKwCase)) {
    state.case_default_counts.push_back(0);
    lexer.Next();
    return true;
  }
  if (LexerCheck(lexer, TokenKind::kKwEndcase)) {
    if (!state.case_default_counts.empty())
      state.case_default_counts.pop_back();
    lexer.Next();
    return true;
  }
  if (LexerCheck(lexer, TokenKind::kKwDefault) &&
      !state.case_default_counts.empty()) {
    // §16.12.16: the default statement is optional, but using more than one
    // default in a single property case statement shall be illegal.
    auto default_loc = lexer.Peek().loc;
    if (++state.case_default_counts.back() == 2) {
      diag.Error(default_loc,
                 "property case statement shall have at most one 'default' "
                 "item");
    }
    lexer.Next();
    return true;
  }
  return false;
}

// §16.12.17 Restrictions 1 & 3: handles the prefix-negation operators and the
// time-advancing operators that update the scan trackers. Returns true if the
// current token was consumed here.
static bool ScanOperatorToken(Lexer& lexer, PropertyBodyScanState& state) {
  // §16.12.17 Restriction 1: the prefix operators not, s_nexttime,
  // s_eventually, and s_always negate/strongly bind the property expression
  // that follows. s_until and s_until_with are infix; their right operand is
  // also a property expression. Mark that the next instance reached is one of
  // these operands. (s_nexttime also advances time for Restriction 3.)
  if (LexerCheck(lexer, TokenKind::kKwNot) ||
      LexerCheck(lexer, TokenKind::kKwSNexttime) ||
      LexerCheck(lexer, TokenKind::kKwSEventually) ||
      LexerCheck(lexer, TokenKind::kKwSAlways) ||
      LexerCheck(lexer, TokenKind::kKwSUntil) ||
      LexerCheck(lexer, TokenKind::kKwSUntilWith)) {
    if (LexerCheck(lexer, TokenKind::kKwSNexttime))
      state.saw_time_advance = true;
    state.expect_negated_operand = true;
    lexer.Next();
    return true;
  }
  // §16.12.17 Restriction 3: ##, |=> (suffix non-overlapping implication),
  // and (s_)nexttime advance time. |-> (overlapping implication) does not.
  if (LexerCheck(lexer, TokenKind::kHashHash) ||
      LexerCheck(lexer, TokenKind::kPipeEqGt) ||
      LexerCheck(lexer, TokenKind::kKwNexttime)) {
    state.saw_time_advance = true;
    lexer.Next();
    return true;
  }
  return false;
}

// Handles an identifier head: a following '(' makes it a property/sequence
// instance reference (recorded, with §16.12.17 negation/self-recursion checks
// and argument capture); otherwise it is a bare expression operand.
static void ScanIdentifierToken(Lexer& lexer, ModuleItem* item,
                                PropertyBodyScanState& state) {
  auto tok = lexer.Next();
  if (LexerCheck(lexer, TokenKind::kLParen)) {
    item->prop_instance_refs.push_back(tok.text);
    if (state.expect_negated_operand) {
      item->prop_negated_instance_refs.push_back(tok.text);
    }
    if (tok.text == item->name && !state.saw_time_advance) {
      item->prop_has_untimed_self_recursion = true;
    }
    state.expect_negated_operand = false;
    CaptureInstanceArgs(lexer, item, tok.text);
  } else {
    // A bare identifier is not a property instance; if it stood as the
    // operand of a pending negation, that operand is a simple expression.
    state.expect_negated_operand = false;
  }
}

// Processes one token of the named-property body scan that is not an assertion
// variable declaration (those are harvested by the caller, which owns the
// member helper). Carries the §16.12 scan state by reference so cross-iteration
// state is preserved exactly as in the original inline loop.
static void ScanPropertyBodyToken(Lexer& lexer, DiagEngine& diag,
                                  ModuleItem* item,
                                  PropertyBodyScanState& state) {
  if (LexerCheck(lexer, TokenKind::kKwDisable)) {
    lexer.Next();
    if (LexerCheck(lexer, TokenKind::kKwIff)) {
      lexer.Next();
      ++item->prop_disable_iff_count;
    }
    return;
  }
  if (ScanCaseDefaultToken(lexer, diag, state)) return;
  if (ScanOperatorToken(lexer, state)) return;
  if (LexerCheck(lexer, TokenKind::kIdentifier)) {
    ScanIdentifierToken(lexer, item, state);
    return;
  }
  // Opening parentheses are skipped so a negation can still reach an instance
  // wrapped in parentheses; any other token ends a pending negation operand.
  if (!LexerCheck(lexer, TokenKind::kLParen))
    state.expect_negated_operand = false;
  lexer.Next();
}

// §16.12 + §F.4.1: capture formal names, body disable-iff count, and nested
// property/sequence instance references so the rewriter has what it needs.
ModuleItem* Parser::ParsePropertyDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kPropertyDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwProperty);
  item->name = Expect(TokenKind::kIdentifier).text;

  if (Match(TokenKind::kLParen)) {
    ParsePropertyPortList(lexer_, diag_, item);
  }

  Expect(TokenKind::kSemicolon);

  // §16.10: assertion_variable_declarations may appear at the head of a
  // property body, just as in a sequence body. Harvest them before the
  // body skip loop falls through to its existing instance-reference scan.
  bool in_decl_prefix = true;
  // §16.12.16/§16.12.17: the case-default stack and the negation/time-advance
  // trackers are the body scan's cross-iteration state. case_default_counts
  // stacks nested `case`..`endcase` default counts; expect_negated_operand
  // marks a pending prefix-negation operand; saw_time_advance records a
  // time-advancing operator before a self-name instantiation.
  PropertyBodyScanState scan_state;

  while (!Check(TokenKind::kKwEndproperty) && !AtEnd()) {
    if (in_decl_prefix && IsBuiltinTypeKwForLocalVar(CurrentToken().kind)) {
      HarvestAssertionVariableDecl(item);
      continue;
    }
    in_decl_prefix = false;
    ScanPropertyBodyToken(lexer_, diag_, item, scan_state);
  }
  Expect(TokenKind::kKwEndproperty);
  MatchEndLabel(item->name);
  return item;
}

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
    expect_formal_name = false;
  }

  // Consumes one token of the port list. Returns false once the matching ')'
  // for the opening '(' has been consumed (list complete).
  bool Step(Lexer& lexer, DiagEngine& diag, ModuleItem* item) {
    if (LexerCheck(lexer, TokenKind::kLParen)) {
      lexer.Next();
      ++depth;
    } else if (LexerCheck(lexer, TokenKind::kRParen)) {
      if (depth == 1) FinalizePortItem(diag, item);
      lexer.Next();
      --depth;
      if (depth == 0) return false;
    } else if (depth == 1 && LexerCheck(lexer, TokenKind::kComma)) {
      FinalizePortItem(diag, item);
      lexer.Next();
      item_start = lexer.Peek().loc;
      ResetAfterComma(lexer);
    } else if (depth == 1 && LexerCheck(lexer, TokenKind::kKwLocal)) {
      if (!item_saw_local) item_start = lexer.Peek().loc;
      item_saw_local = true;
      item_local_explicit_here = true;
      lexer.Next();
    } else if (depth == 1 && (LexerCheck(lexer, TokenKind::kKwInput) ||
                              LexerCheck(lexer, TokenKind::kKwOutput) ||
                              LexerCheck(lexer, TokenKind::kKwInout))) {
      HandleDirection(lexer, diag);
    } else if (depth == 1 && IsBuiltinTypeKwForLocalVar(lexer.Peek().kind)) {
      lexer.Next();
      item_saw_explicit_type = true;
    } else if (depth == 1 && LexerCheck(lexer, TokenKind::kEq)) {
      item_saw_eq = true;
      lexer.Next();
      expect_formal_name = false;
    } else if (depth == 1 && expect_formal_name &&
               LexerCheck(lexer, TokenKind::kIdentifier)) {
      HarvestFormalName(lexer, item);
    } else {
      lexer.Next();
    }
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

  // §16.10: assertion_variable_declarations precede the sequence_expr in the
  // body. We harvest them while still at the head of the body; once we see a
  // token that does not start a declaration we fall through to the existing
  // sequence_instance reference scan used for the §16.8 cycle rule.
  bool in_decl_prefix = true;
  while (!Check(TokenKind::kKwEndsequence) && !AtEnd()) {
    if (in_decl_prefix && IsBuiltinTypeKwForLocalVar(CurrentToken().kind)) {
      HarvestAssertionVariableDecl(item);
      continue;
    }
    in_decl_prefix = false;

    if (Check(TokenKind::kHashHash)) {
      auto delay_loc = CurrentLoc();
      Consume();
      ValidateLiteralCycleDelayRange(delay_loc);
      continue;
    }
    if (Check(TokenKind::kIdentifier)) {
      auto tok = Consume();
      item->prop_instance_refs.push_back(tok.text);
      continue;
    }
    Consume();
  }
  Expect(TokenKind::kKwEndsequence);
  MatchEndLabel(item->name);
  return item;
}

}  // namespace delta
