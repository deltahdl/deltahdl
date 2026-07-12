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
  // §16.12.18: whether the current formal item was introduced with the type
  // keyword `property`. Like `local`, the property_formal_type qualifies the
  // whole comma-separated run of names until a fresh, differently typed item
  // begins.
  bool property_run = false;
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
    item->prop_formal_is_property.push_back(property_run);
    expect_formal_name = false;
    saw_local = false;
  }

  // depth==1 built-in type keyword: a built-in type keyword that does not
  // directly follow `local` or `input` starts a fresh formal item whose
  // qualifiers do not include `local`, so the local-variable run ends here.
  void HandleBuiltinTypeKw(Lexer& lexer) {
    if (prev_kind != TokenKind::kKwLocal && prev_kind != TokenKind::kKwInput) {
      local_run = false;
    }
    // §16.12.18: a data-type formal (one of the §16.6 types) is not a
    // `property` formal, so the property run ends where such a type specifier
    // begins.
    property_run = false;
    lexer.Next();
  }

  // §16.12.18: the `property` type keyword begins a run of one or more
  // property-typed formal arguments. A property formal is never a local
  // variable formal, so the local run ends here.
  void HandlePropertyTypeKw(Lexer& lexer) {
    property_run = true;
    local_run = false;
    saw_local = false;
    lexer.Next();
  }

  // §16.12.18: the `sequence`, `event`, and `untyped` type keywords begin a
  // differently typed formal item, ending any in-progress property (and local)
  // run.
  void HandleNonPropertyTypeKw(Lexer& lexer) {
    property_run = false;
    local_run = false;
    saw_local = false;
    lexer.Next();
  }

  // §16.12.19: a local variable formal argument of a named property shall have
  // direction `input`; declaring one with direction `inout` or `output` is
  // illegal. The borrowed A.2.10 production property_lvar_port_direction admits
  // only `input`, so `output` and `inout` have no legal role inside a property
  // port, with or without a preceding `local`.
  void HandleIllegalDirection(Lexer& lexer, DiagEngine& diag) {
    diag.Error(lexer.Peek().loc, "property port direction must be 'input'");
    lexer.Next();
    saw_local = false;
  }

  // `input` is permitted only after `local`.
  void HandleInputDirection(Lexer& lexer, DiagEngine& diag) {
    if (!saw_local) {
      diag.Error(lexer.Peek().loc,
                 "property port direction 'input' requires 'local'");
    }
    lexer.Next();
    saw_local = false;
  }

  // Handles the depth==1 (top-level) tokens of the property port list. Returns
  // true if the current token was consumed here; false means the caller falls
  // through to the default skip. All branches assume depth==1 already holds.
  bool DispatchTopLevel(Lexer& lexer, DiagEngine& diag, ModuleItem* item) {
    if (LexerCheck(lexer, TokenKind::kComma)) {
      lexer.Next();
      expect_formal_name = true;
      saw_local = false;
    } else if (LexerCheck(lexer, TokenKind::kEq)) {
      lexer.Next();
      expect_formal_name = false;
    } else if (LexerCheck(lexer, TokenKind::kKwLocal)) {
      lexer.Next();
      saw_local = true;
      local_run = true;
    } else if (IsBuiltinTypeKwForLocalVar(lexer.Peek().kind)) {
      HandleBuiltinTypeKw(lexer);
    } else if (LexerCheck(lexer, TokenKind::kKwProperty)) {
      HandlePropertyTypeKw(lexer);
    } else if (LexerCheck(lexer, TokenKind::kKwSequence) ||
               LexerCheck(lexer, TokenKind::kKwEvent) ||
               LexerCheck(lexer, TokenKind::kKwUntyped)) {
      HandleNonPropertyTypeKw(lexer);
    } else if (LexerCheck(lexer, TokenKind::kKwOutput) ||
               LexerCheck(lexer, TokenKind::kKwInout)) {
      HandleIllegalDirection(lexer, diag);
    } else if (LexerCheck(lexer, TokenKind::kKwInput)) {
      HandleInputDirection(lexer, diag);
    } else if (expect_formal_name &&
               LexerCheck(lexer, TokenKind::kIdentifier)) {
      HarvestFormalName(lexer, item);
    } else {
      return false;
    }
    return true;
  }

  // Dispatches one token to its handler, updating scan state. Returns false
  // once the matching ')' for the opening '(' has been consumed.
  bool Dispatch(Lexer& lexer, DiagEngine& diag, ModuleItem* item) {
    if (LexerCheck(lexer, TokenKind::kLParen)) {
      lexer.Next();
      ++depth;
      return true;
    }
    if (LexerCheck(lexer, TokenKind::kRParen)) {
      lexer.Next();
      --depth;
      return depth != 0;
    }
    if (depth == 1 && DispatchTopLevel(lexer, diag, item)) return true;
    lexer.Next();
    return true;
  }

  // Consumes one token of the port list. Returns false once the matching ')'
  // for the opening '(' has been consumed (list complete).
  bool Step(Lexer& lexer, DiagEngine& diag, ModuleItem* item) {
    TokenKind this_kind = lexer.Peek().kind;
    bool keep_going = Dispatch(lexer, diag, item);
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

// §16.12.10: the indexed nexttime forms `nexttime [ constant_expression ]` and
// `s_nexttime [ constant_expression ]` carry a bracketed tick count that shall
// be a non-negative integer constant expression. Like the literal cycle-delay
// range check (§16.7), only the literal `[ [-] INTLIT ]` form is diagnosed
// here: a negative integer literal index violates the non-negative requirement
// and is rejected, while a symbolic index (for example a parameter) needs full
// constant folding and is deferred to later stages. The bracket tokens are only
// peeked under SavePos, so the surrounding body scan still walks past them.
// Called with the current token positioned on the opening '['.
static void ValidateLiteralNexttimeIndex(Lexer& lexer, DiagEngine& diag) {
  auto index_loc = lexer.Peek().loc;
  auto saved = lexer.SavePos();
  lexer.Next();  // [
  bool negative = false;
  if (LexerCheck(lexer, TokenKind::kMinus)) {
    negative = true;
    lexer.Next();
  }
  bool is_int_literal = LexerCheck(lexer, TokenKind::kIntLiteral);
  lexer.RestorePos(saved);

  // §16.12.10: a negative integer literal tick count is illegal. Non-literal
  // (symbolic) indices are left for the constant-folding stages.
  if (negative && is_int_literal) {
    diag.Error(index_loc,
               "nexttime index must be a non-negative integer constant "
               "expression (§16.12.10)");
  }
}

// §16.12.11: validate the bracketed range of a ranged always property. As with
// the §16.7 cycle-delay range and the §16.12.10 nexttime index, only the
// literal `[ [-]INTLIT [ : [-]INTLIT | : $ ] ]` form is diagnosed here; a
// symbolic bound (for example a parameter) needs full constant folding and is
// deferred to later stages. The minimum shall be a non-negative integer
// constant expression and the maximum shall be a non-negative integer constant
// expression or `$`. When both bounds are non-negative integer constant
// literals the minimum shall not exceed the maximum. The range for a strong
// always shall be bounded, so a `$` maximum is illegal for `s_always` while it
// is allowed for a weak always. The bracket tokens are only peeked under
// SavePos so the body scan still walks past them. Called with the current token
// positioned on the opening '['.
static void ValidateLiteralAlwaysRange(Lexer& lexer, DiagEngine& diag,
                                       bool strong) {
  auto range_loc = lexer.Peek().loc;
  auto saved = lexer.SavePos();
  lexer.Next();  // [
  bool min_negative = false;
  if (LexerCheck(lexer, TokenKind::kMinus)) {
    min_negative = true;
    lexer.Next();
  }
  bool min_is_literal = LexerCheck(lexer, TokenKind::kIntLiteral);
  std::string min_text;
  if (min_is_literal) {
    min_text = std::string(lexer.Peek().text);
    lexer.Next();
  }
  bool max_negative = false;
  bool max_is_literal = false;
  bool max_is_dollar = false;
  std::string max_text;
  if (LexerCheck(lexer, TokenKind::kColon)) {
    lexer.Next();  // :
    if (LexerCheck(lexer, TokenKind::kMinus)) {
      max_negative = true;
      lexer.Next();
    }
    if (LexerCheck(lexer, TokenKind::kDollar)) {
      max_is_dollar = true;
    } else if (LexerCheck(lexer, TokenKind::kIntLiteral)) {
      max_is_literal = true;
      max_text = std::string(lexer.Peek().text);
    }
  }
  lexer.RestorePos(saved);

  // §16.12.11: a negative integer literal on either bound violates the
  // non-negative integer constant expression requirement.
  if ((min_negative && min_is_literal) || (max_negative && max_is_literal)) {
    diag.Error(range_loc,
               "always range bounds must be non-negative integer constant "
               "expressions (§16.12.11)");
    return;
  }
  // §16.12.11: when both bounds are non-negative integer constant literals the
  // minimum shall not exceed the maximum. Only plain decimal literals are
  // compared; sized or based literals need full constant evaluation and are
  // deferred, matching the §16.7 cycle-delay range check.
  if (min_is_literal && max_is_literal) {
    auto plain_decimal = [](const std::string& text, uint64_t& out) -> bool {
      uint64_t value = 0;
      bool saw_digit = false;
      for (char c : text) {
        if (c == '_') continue;
        if (c < '0' || c > '9') return false;
        saw_digit = true;
        value = value * 10 + static_cast<uint64_t>(c - '0');
      }
      if (!saw_digit) return false;
      out = value;
      return true;
    };
    uint64_t min_mag = 0;
    uint64_t max_mag = 0;
    if (plain_decimal(min_text, min_mag) && plain_decimal(max_text, max_mag) &&
        min_mag > max_mag) {
      diag.Error(
          range_loc,
          "always range minimum must not exceed the maximum (§16.12.11)");
      return;
    }
  }
  // §16.12.11: a strong always range shall be bounded, so a `$` maximum is
  // rejected for s_always even though it is legal for a weak always.
  if (strong && max_is_dollar) {
    diag.Error(range_loc,
               "s_always range shall be bounded; a `$` maximum is not allowed "
               "(§16.12.11)");
  }
}

// §16.12.13: validate the bracketed range of a ranged eventually property. The
// weak form carries a constant_range and the strong form a
// cycle_delay_const_range_expression, but both share the literal shape
// `[ [-]INTLIT [ : [-]INTLIT | : $ ] ]`. As with the §16.7 cycle-delay range
// and the §16.12.11 always range, only that literal form is diagnosed here; a
// symbolic bound (for example a parameter) needs full constant folding and is
// deferred to later stages. Both bounds shall be non-negative integer constant
// expressions, and when both are non-negative integer constant literals the
// minimum shall not exceed the maximum. The polarity of the boundedness rule is
// the reverse of §16.12.11: the range for a weak `eventually` shall be bounded,
// so a `$` maximum is illegal there (the `eventually [2:$]` form is illegal),
// while the range for a strong `s_eventually` may be unbounded, so a `$`
// maximum is accepted. The bracket tokens are only peeked under SavePos so the
// body scan still walks past them. Called with the current token positioned on
// the opening '['.
static void ValidateLiteralEventuallyRange(Lexer& lexer, DiagEngine& diag,
                                           bool strong) {
  auto range_loc = lexer.Peek().loc;
  auto saved = lexer.SavePos();
  lexer.Next();  // [
  bool min_negative = false;
  if (LexerCheck(lexer, TokenKind::kMinus)) {
    min_negative = true;
    lexer.Next();
  }
  bool min_is_literal = LexerCheck(lexer, TokenKind::kIntLiteral);
  std::string min_text;
  if (min_is_literal) {
    min_text = std::string(lexer.Peek().text);
    lexer.Next();
  }
  bool max_negative = false;
  bool max_is_literal = false;
  bool max_is_dollar = false;
  std::string max_text;
  if (LexerCheck(lexer, TokenKind::kColon)) {
    lexer.Next();  // :
    if (LexerCheck(lexer, TokenKind::kMinus)) {
      max_negative = true;
      lexer.Next();
    }
    if (LexerCheck(lexer, TokenKind::kDollar)) {
      max_is_dollar = true;
    } else if (LexerCheck(lexer, TokenKind::kIntLiteral)) {
      max_is_literal = true;
      max_text = std::string(lexer.Peek().text);
    }
  }
  lexer.RestorePos(saved);

  // §16.12.13: a negative integer literal on either bound violates the
  // non-negative integer constant expression requirement.
  if ((min_negative && min_is_literal) || (max_negative && max_is_literal)) {
    diag.Error(range_loc,
               "eventually range bounds must be non-negative integer constant "
               "expressions (§16.12.13)");
    return;
  }
  // §16.12.13: when both bounds are non-negative integer constant literals the
  // minimum shall not exceed the maximum. Only plain decimal literals are
  // compared; sized or based literals need full constant evaluation and are
  // deferred, matching the §16.7 cycle-delay range check.
  if (min_is_literal && max_is_literal) {
    auto plain_decimal = [](const std::string& text, uint64_t& out) -> bool {
      uint64_t value = 0;
      bool saw_digit = false;
      for (char c : text) {
        if (c == '_') continue;
        if (c < '0' || c > '9') return false;
        saw_digit = true;
        value = value * 10 + static_cast<uint64_t>(c - '0');
      }
      if (!saw_digit) return false;
      out = value;
      return true;
    };
    uint64_t min_mag = 0;
    uint64_t max_mag = 0;
    if (plain_decimal(min_text, min_mag) && plain_decimal(max_text, max_mag) &&
        min_mag > max_mag) {
      diag.Error(
          range_loc,
          "eventually range minimum must not exceed the maximum (§16.12.13)");
      return;
    }
  }
  // §16.12.13: a weak eventually range shall be bounded, so a `$` maximum is
  // rejected for `eventually` even though the same maximum is legal for the
  // strong `s_eventually`, whose range may be unbounded.
  if (!strong && max_is_dollar) {
    diag.Error(
        range_loc,
        "eventually range shall be bounded; a `$` maximum is not allowed "
        "for weak eventually (§16.12.13)");
  }
}

// §16.12.17 Restrictions 1 & 3: handles the prefix-negation operators and the
// time-advancing operators that update the scan trackers. Returns true if the
// current token was consumed here.
static bool ScanOperatorToken(Lexer& lexer, DiagEngine& diag,
                              PropertyBodyScanState& state) {
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
    bool is_s_nexttime = LexerCheck(lexer, TokenKind::kKwSNexttime);
    bool is_s_always = LexerCheck(lexer, TokenKind::kKwSAlways);
    bool is_s_eventually = LexerCheck(lexer, TokenKind::kKwSEventually);
    if (is_s_nexttime) state.saw_time_advance = true;
    state.expect_negated_operand = true;
    lexer.Next();
    // §16.12.10: validate the strong indexed form `s_nexttime [ c ]`. The other
    // bracketed operators in this group carry ranges: s_always's
    // constant_range is checked under §16.12.11, and s_eventually's
    // cycle_delay_const_range_expression under §16.12.13 — the latter
    // permitting an unbounded `$` maximum that the weak forms forbid.
    if (is_s_nexttime && LexerCheck(lexer, TokenKind::kLBracket))
      ValidateLiteralNexttimeIndex(lexer, diag);
    else if (is_s_always && LexerCheck(lexer, TokenKind::kLBracket))
      ValidateLiteralAlwaysRange(lexer, diag, /*strong=*/true);
    else if (is_s_eventually && LexerCheck(lexer, TokenKind::kLBracket))
      ValidateLiteralEventuallyRange(lexer, diag, /*strong=*/true);
    return true;
  }
  // §16.12.11: the weak `always` prefix admits a ranged form carrying a
  // cycle_delay_const_range_expression. It is neither a negation nor a
  // time-advancing operator for §16.12.17, so it is consumed here solely to
  // validate the range literal. Resetting the pending-negation flag mirrors the
  // generic token handling `always` previously fell through to, keeping the
  // §16.12.17 scan state unchanged.
  if (LexerCheck(lexer, TokenKind::kKwAlways)) {
    state.expect_negated_operand = false;
    lexer.Next();
    if (LexerCheck(lexer, TokenKind::kLBracket))
      ValidateLiteralAlwaysRange(lexer, diag, /*strong=*/false);
    return true;
  }
  // §16.12.13: the weak `eventually` prefix admits only a ranged form, and that
  // range shall be bounded (a `$` maximum is illegal). Like weak `always`, it
  // is neither a negation nor a time-advancing operator for §16.12.17, so it is
  // consumed here solely to validate the range literal. Resetting the
  // pending-negation flag mirrors the generic token handling `eventually`
  // otherwise falls through to, leaving the §16.12.17 scan state unchanged.
  if (LexerCheck(lexer, TokenKind::kKwEventually)) {
    state.expect_negated_operand = false;
    lexer.Next();
    if (LexerCheck(lexer, TokenKind::kLBracket))
      ValidateLiteralEventuallyRange(lexer, diag, /*strong=*/false);
    return true;
  }
  // §16.12.17 Restriction 3: ##, |=> (suffix non-overlapping implication),
  // and (s_)nexttime advance time. |-> (overlapping implication) does not.
  if (LexerCheck(lexer, TokenKind::kHashHash) ||
      LexerCheck(lexer, TokenKind::kPipeEqGt) ||
      LexerCheck(lexer, TokenKind::kKwNexttime)) {
    bool is_nexttime = LexerCheck(lexer, TokenKind::kKwNexttime);
    state.saw_time_advance = true;
    lexer.Next();
    // §16.12.10: validate the weak indexed form `nexttime [ c ]`.
    if (is_nexttime && LexerCheck(lexer, TokenKind::kLBracket))
      ValidateLiteralNexttimeIndex(lexer, diag);
    return true;
  }
  return false;
}

// §16.12.18: reports whether `name` was declared as a `property`-typed formal
// of this named property. The is-property flags are recorded in parallel with
// the formal names during the port-list scan.
static bool IsPropertyTypedFormal(const ModuleItem* item,
                                  std::string_view name) {
  for (size_t i = 0; i < item->prop_formals.size(); ++i) {
    if (item->prop_formals[i] == name &&
        i < item->prop_formal_is_property.size() &&
        item->prop_formal_is_property[i]) {
      return true;
    }
  }
  return false;
}

// Handles an identifier head: a following '(' makes it a property/sequence
// instance reference (recorded, with §16.12.17 negation/self-recursion checks
// and argument capture); otherwise it is a bare expression operand.
static void ScanIdentifierToken(Lexer& lexer, DiagEngine& diag,
                                ModuleItem* item,
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
    // §16.12.18: a formal argument of type `property` may not be referenced as
    // the antecedent of an overlapping (`|->`) or non-overlapping (`|=>`)
    // implication (see §16.12.7), regardless of the actual argument bound to
    // it, because a property_expr may not be written in the antecedent
    // position. When such a bare formal reference is immediately followed by an
    // implication operator, it stands in that forbidden antecedent position.
    if ((LexerCheck(lexer, TokenKind::kPipeDashGt) ||
         LexerCheck(lexer, TokenKind::kPipeEqGt)) &&
        IsPropertyTypedFormal(item, tok.text)) {
      diag.Error(tok.loc,
                 "a 'property'-typed formal argument may not be referenced as "
                 "the antecedent of '|->' or '|=>' (§16.12.18)");
    }
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
  if (ScanOperatorToken(lexer, diag, state)) return;
  if (LexerCheck(lexer, TokenKind::kIdentifier)) {
    ScanIdentifierToken(lexer, diag, item, state);
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
    TokenKind k = CurrentToken().kind;
    if (k == TokenKind::kLParen || k == TokenKind::kLBracket ||
        k == TokenKind::kLBrace) {
      ++nesting;
    } else if (k == TokenKind::kRParen || k == TokenKind::kRBracket ||
               k == TokenKind::kRBrace) {
      --nesting;
    } else if (nesting == 1 && k == TokenKind::kQuestion) {
      ++cond_depth;
    } else if (nesting == 1 && k == TokenKind::kColon) {
      if (cond_depth > 0) {
        --cond_depth;  // the ':' of a conditional, not a min:typ:max separator.
      } else {
        is_min_typ_max = true;
      }
    }
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
    } else if (LexerCheck(lexer, TokenKind::kEq)) {
      item_saw_eq = true;
      // §16.8: `formal = default_expression` gives the most recently harvested
      // formal a default actual argument.
      if (!item->prop_formal_has_default.empty()) {
        item->prop_formal_has_default.back() = true;
      }
      lexer.Next();
      expect_formal_name = false;
    } else if (expect_formal_name &&
               LexerCheck(lexer, TokenKind::kIdentifier)) {
      HarvestFormalName(lexer, item);
    } else {
      return false;
    }
    return true;
  }

  // Consumes one token of the port list. Returns false once the matching ')'
  // for the opening '(' has been consumed (list complete).
  bool Step(Lexer& lexer, DiagEngine& diag, ModuleItem* item) {
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

  // §16.13.6: capture the simple clocked linear body for the simulator's
  // sequence.triggered monitor. This is a trial parse that suppresses
  // diagnostics and rewinds, so the harvest scan below runs over the same
  // tokens unchanged.
  CaptureLinearSequenceBody(item);

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

    // §16.10: a local variable declared in the sequence body cannot be used in
    // the body's clocking event expression. The assertion_variable_declarations
    // are harvested before this point, so any identifier inside a `@( ... )`
    // event group (an edge signal or an iff guard) that matches a body local is
    // rejected here. The whole parenthesized event group is consumed so its
    // names are not also recorded as sequence instance references.
    if (Check(TokenKind::kAt)) {
      Consume();  // '@'
      if (Check(TokenKind::kLParen)) {
        Consume();  // '('
        int depth = 1;
        while (depth > 0 && !AtEnd()) {
          if (Check(TokenKind::kLParen)) {
            ++depth;
          } else if (Check(TokenKind::kRParen)) {
            --depth;
          } else if (Check(TokenKind::kIdentifier)) {
            auto name = CurrentToken().text;
            for (auto local : item->prop_seq_assert_vars) {
              if (local == name) {
                diag_.Error(CurrentLoc(),
                            "local variable \"" + std::string(name) +
                                "\" may not be used in a clocking event "
                                "expression (§16.10)");
                break;
              }
            }
          }
          Consume();
        }
      }
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
