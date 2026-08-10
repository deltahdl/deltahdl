#include <format>
#include <string>
#include <string_view>

#include "parser/parser.h"
#include "parser/parser_sequence_property_decl_internal.h"

namespace delta {

// Replicates Parser::Check directly against a Lexer so the free-function
// helpers in this file see the same identifier/escaped-identifier folding the
// member helpers use.
bool LexerCheck(Lexer& lexer, TokenKind kind) {
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
bool IsBuiltinTypeKwForLocalVar(TokenKind k) {
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

// §16.8.2: the type of a local variable formal argument shall be one of the
// types allowed in §16.6. The formal-type categories that §16.8.1 permits for
// an ordinary (non-local) formal — `sequence`, `event`, `property`, and the
// keyword `untyped` — are not among the §16.6 data types, so specifying one of
// them as the type of a `local` formal is illegal (the illegal example in
// §16.8.2 rejects `local event e` on exactly these grounds). These keywords are
// recognised head-on so the diagnostic names the real problem (a disallowed
// type) rather than being mistaken for a missing type.
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
  // §16.14.7: whether the current formal run admits a $inferred_clock default.
  // $inferred_clock may only default a formal that is untyped or of type
  // `event`. A run introduced by `event`/`untyped` (or the initial no-type run)
  // permits it; a data type, `sequence`, or `property` formal does not. Follows
  // the same comma-run persistence as the type qualifiers above.
  bool clock_default_allowed = true;
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
    // §16.14.7: a data-typed formal is neither untyped nor `event`, so it may
    // not be defaulted to $inferred_clock.
    clock_default_allowed = false;
    lexer.Next();
  }

  // §16.12.18: the `property` type keyword begins a run of one or more
  // property-typed formal arguments. A property formal is never a local
  // variable formal, so the local run ends here.
  void HandlePropertyTypeKw(Lexer& lexer) {
    property_run = true;
    local_run = false;
    saw_local = false;
    // §16.14.7: a `property`-typed formal is neither untyped nor `event`, so it
    // may not be defaulted to $inferred_clock.
    clock_default_allowed = false;
    lexer.Next();
  }

  // §16.12.18: the `sequence`, `event`, and `untyped` type keywords begin a
  // differently typed formal item, ending any in-progress property (and local)
  // run.
  void HandleNonPropertyTypeKw(Lexer& lexer) {
    // §16.14.7: `event` and `untyped` formals admit a $inferred_clock default;
    // `sequence` (the other keyword routed here) does not.
    TokenKind kw = lexer.Peek().kind;
    clock_default_allowed =
        kw == TokenKind::kKwEvent || kw == TokenKind::kKwUntyped;
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
    diag.Error(lexer.Peek().loc, "property port direction must be 'input'",
               Subclause("16.12.19"));
    lexer.Next();
    saw_local = false;
  }

  // `input` is permitted only after `local`.
  void HandleInputDirection(Lexer& lexer, DiagEngine& diag) {
    if (!saw_local) {
      diag.Error(lexer.Peek().loc,
                 "property port direction 'input' requires 'local'",
                 Subclause("16.12.19"));
    }
    lexer.Next();
    saw_local = false;
  }

  // Handles the depth==1 (top-level) tokens of the property port list. Returns
  // true if the current token was consumed here; false means the caller falls
  // through to the default skip. All branches assume depth==1 already holds.
  // §16.14.7: a system-function name that opens a formal's default value (it
  // directly follows `=`). $inferred_clock shall only default a formal that is
  // untyped or of type `event`, so it is rejected on a data-typed, `sequence`,
  // or `property` formal. An inferred clocking or disable function shall also
  // be the entire default value expression: if any further token of the default
  // follows the call (the next token is neither the formal separator ',' nor
  // the port list's closing ')'), it is only part of a larger expression.
  void HandleSystemDefaultValue(Lexer& lexer, DiagEngine& diag) {
    auto fn = lexer.Peek().text;
    auto fn_loc = lexer.Peek().loc;
    bool is_inferred = fn == "$inferred_clock" || fn == "$inferred_disable";
    if (fn == "$inferred_clock" && !clock_default_allowed) {
      diag.Error(fn_loc,
                 "$inferred_clock default requires an untyped or event "
                 "formal argument",
                 Subclause("16.14.7"));
    }
    lexer.Next();
    if (is_inferred && !LexerCheck(lexer, TokenKind::kComma) &&
        !LexerCheck(lexer, TokenKind::kRParen)) {
      diag.Error(fn_loc,
                 "an inferred clocking or disable function must be the "
                 "entire default value of a formal argument",
                 Subclause("16.14.7"));
    }
  }

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
                 "item",
                 Subclause("16.12.16"));
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
               "expression",
               Subclause("16.12.10"));
  }
}

// The literal shape a bracketed property range may take:
// `[ [-]INTLIT [ : [-]INTLIT | : $ ] ]`. Only this form is diagnosed in the
// parser -- a symbolic bound (for example a parameter) needs full constant
// folding and is deferred to later stages -- so each field records what was
// literally seen rather than a folded value.
struct LiteralRangeBounds {
  SourceLoc loc;  // the opening '[', which a diagnostic is anchored at
  bool min_negative = false;
  bool min_is_literal = false;
  bool max_negative = false;
  bool max_is_literal = false;
  bool max_is_dollar = false;
  std::string min_text;
  std::string max_text;
};

// Reports the literal shape of the bracketed range the lexer is positioned on.
// The tokens are only peeked under SavePos, so the lexer is left where it
// started and the surrounding body scan still walks past them. A range with no
// `:` leaves every max field clear. Called with the current token positioned on
// the opening '['.
static LiteralRangeBounds ScanLiteralRange(Lexer& lexer) {
  LiteralRangeBounds r;
  r.loc = lexer.Peek().loc;
  auto saved = lexer.SavePos();
  lexer.Next();  // [
  if (LexerCheck(lexer, TokenKind::kMinus)) {
    r.min_negative = true;
    lexer.Next();
  }
  r.min_is_literal = LexerCheck(lexer, TokenKind::kIntLiteral);
  if (r.min_is_literal) {
    r.min_text = std::string(lexer.Peek().text);
    lexer.Next();
  }
  if (LexerCheck(lexer, TokenKind::kColon)) {
    lexer.Next();  // :
    if (LexerCheck(lexer, TokenKind::kMinus)) {
      r.max_negative = true;
      lexer.Next();
    }
    if (LexerCheck(lexer, TokenKind::kDollar)) {
      r.max_is_dollar = true;
    } else if (LexerCheck(lexer, TokenKind::kIntLiteral)) {
      r.max_is_literal = true;
      r.max_text = std::string(lexer.Peek().text);
    }
  }
  lexer.RestorePos(saved);
  return r;
}

// Reads a plain decimal integer literal's magnitude. A sized or based literal
// needs full constant evaluation, so it is not compared here and yields false.
static bool PlainDecimalMagnitude(const std::string& text, uint64_t& out) {
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
}

// The two rules every bracketed property range shares: both bounds shall be
// non-negative integer constant expressions, and when both are non-negative
// integer constant literals the minimum shall not exceed the maximum. `what`
// names the property in the diagnostic and `subclause` the subclause stating
// the rule for it. Returns false once a violation has been reported, so a
// caller stops before applying its own boundedness rule.
static bool CheckLiteralRangeBounds(const LiteralRangeBounds& r,
                                    DiagEngine& diag, std::string_view what,
                                    Subclause subclause) {
  if ((r.min_negative && r.min_is_literal) ||
      (r.max_negative && r.max_is_literal)) {
    diag.Error(r.loc,
               std::format("{} range bounds must be non-negative integer "
                           "constant expressions",
                           what),
               subclause);
    return false;
  }
  if (r.min_is_literal && r.max_is_literal) {
    uint64_t min_mag = 0;
    uint64_t max_mag = 0;
    if (PlainDecimalMagnitude(r.min_text, min_mag) &&
        PlainDecimalMagnitude(r.max_text, max_mag) && min_mag > max_mag) {
      diag.Error(
          r.loc,
          std::format("{} range minimum must not exceed the maximum", what),
          subclause);
      return false;
    }
  }
  return true;
}

// §16.12.11: validate the bracketed range of a ranged always property. Beyond
// the bounds rules every property range shares, the range for a strong always
// shall be bounded, so a `$` maximum is illegal for `s_always` while it is
// allowed for a weak always. Called with the current token positioned on the
// opening '['.
static void ValidateLiteralAlwaysRange(Lexer& lexer, DiagEngine& diag,
                                       bool strong) {
  auto r = ScanLiteralRange(lexer);
  if (!CheckLiteralRangeBounds(r, diag, "always", Subclause("16.12.11")))
    return;
  if (strong && r.max_is_dollar) {
    diag.Error(r.loc,
               "s_always range shall be bounded; a `$` maximum is not allowed",
               Subclause("16.12.11"));
  }
}

// §16.12.13: validate the bracketed range of a ranged eventually property. The
// weak form carries a constant_range and the strong form a
// cycle_delay_const_range_expression, but both share the literal shape. Beyond
// the bounds rules every property range shares, the polarity of the
// boundedness rule is the reverse of §16.12.11: the range for a weak
// `eventually` shall be bounded, so a `$` maximum is illegal there (the
// `eventually [2:$]` form is illegal), while the range for a strong
// `s_eventually` may be unbounded. Called with the current token positioned on
// the opening '['.
static void ValidateLiteralEventuallyRange(Lexer& lexer, DiagEngine& diag,
                                           bool strong) {
  auto r = ScanLiteralRange(lexer);
  if (!CheckLiteralRangeBounds(r, diag, "eventually", Subclause("16.12.13")))
    return;
  if (!strong && r.max_is_dollar) {
    diag.Error(r.loc,
               "eventually range shall be bounded; a `$` maximum is not "
               "allowed for weak eventually",
               Subclause("16.12.13"));
  }
}

// §16.12.17 Restrictions 1 & 3: handles the prefix-negation operators and the
// time-advancing operators that update the scan trackers. Returns true if the
// current token was consumed here.
// Consume one of the strong prefix/infix property operators and validate its
// bracketed operand. §16.12.10: the strong indexed form is `s_nexttime [ c ]`.
// The other bracketed operators in this group carry ranges: s_always's
// constant_range is checked under §16.12.11, and s_eventually's
// cycle_delay_const_range_expression under §16.12.13 -- the latter permitting
// an unbounded `$` maximum that the weak forms forbid.
static void ScanStrongPropertyOperator(Lexer& lexer, DiagEngine& diag,
                                       PropertyBodyScanState& state) {
  bool is_s_nexttime = LexerCheck(lexer, TokenKind::kKwSNexttime);
  bool is_s_always = LexerCheck(lexer, TokenKind::kKwSAlways);
  bool is_s_eventually = LexerCheck(lexer, TokenKind::kKwSEventually);
  if (is_s_nexttime) state.saw_time_advance = true;
  state.expect_negated_operand = true;
  lexer.Next();
  if (!LexerCheck(lexer, TokenKind::kLBracket)) return;
  if (is_s_nexttime)
    ValidateLiteralNexttimeIndex(lexer, diag);
  else if (is_s_always)
    ValidateLiteralAlwaysRange(lexer, diag, /*strong=*/true);
  else if (is_s_eventually)
    ValidateLiteralEventuallyRange(lexer, diag, /*strong=*/true);
}

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
    ScanStrongPropertyOperator(lexer, diag, state);
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
    // §16.12.17 Restriction 3: an instance reached before any positive time
    // advance is a zero-weight out-edge. The direct self-loop is flagged
    // outright; every zero-weight edge is also recorded so the elaborator can
    // reject zero-weight mutual-recursion cycles, not only direct ones.
    if (!state.saw_time_advance) {
      item->prop_untimed_instance_refs.push_back(tok.text);
      if (tok.text == item->name) {
        item->prop_has_untimed_self_recursion = true;
      }
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
                 "the antecedent of '|->' or '|=>'",
                 Subclause("16.12.18"));
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
  // §16.16(b2): an `@(...)` in the property body is an explicit clocking event.
  // Count it (the following parenthesized event group is consumed as ordinary
  // tokens by later iterations) so a multiclocked property can be recognized.
  if (LexerCheck(lexer, TokenKind::kAt)) {
    ++item->decl_clock_event_count;
    lexer.Next();
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
  Expect(TokenKind::kKwProperty, Subclause("16.12"));
  item->name = Expect(TokenKind::kIdentifier, Subclause("16.12")).text;

  if (Match(TokenKind::kLParen)) {
    ParsePropertyPortList(lexer_, diag_, item);
  }

  Expect(TokenKind::kSemicolon, Subclause("16.12"));

  // §16.16(b1): a property_spec may open with an explicit leading clocking
  // event. Record its presence (the body's first token is `@`) so a clocking
  // block, which forbids such an event on the declarations it contains, can
  // reject it.
  item->decl_has_leading_clock = Check(TokenKind::kAt);

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
  Expect(TokenKind::kKwEndproperty, Subclause("16.12"));
  MatchEndLabel(item->name);
  return item;
}

}  // namespace delta
