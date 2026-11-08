#include <cstddef>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/parser.h"
#include "parser/parser_property_grammar.h"
#include "parser/parser_property_spec_internal.h"
#include "parser/parser_sequence_property_decl_internal.h"

namespace delta {

bool LexerCheck(Lexer& lexer, TokenKind kind) {
  auto cur = lexer.Peek().kind;
  if (kind == TokenKind::kIdentifier) {
    return cur == TokenKind::kIdentifier ||
           cur == TokenKind::kEscapedIdentifier;
  }
  return cur == kind;
}

bool IsLocalVariableOfDecl(const ModuleItem* item, std::string_view name) {
  for (auto local : item->prop_seq_assert_vars) {
    if (local == name) return true;
  }
  for (size_t i = 0; i < item->prop_formals.size(); ++i) {
    if (item->prop_formals[i] == name &&
        i < item->prop_formal_is_local.size() &&
        item->prop_formal_is_local[i]) {
      return true;
    }
  }
  return false;
}

void ScanClockEventGroupForLocals(Lexer& lexer, DiagEngine& diag,
                                  const ModuleItem* item) {
  if (!LexerCheck(lexer, TokenKind::kLParen)) return;
  lexer.Next();
  int depth = 1;
  while (depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (LexerCheck(lexer, TokenKind::kLParen)) {
      ++depth;
    } else if (LexerCheck(lexer, TokenKind::kRParen)) {
      --depth;
    } else if (LexerCheck(lexer, TokenKind::kIdentifier) &&
               IsLocalVariableOfDecl(item, lexer.Peek().text)) {
      diag.Error(lexer.Peek().loc,
                 "local variable \"" + std::string(lexer.Peek().text) +
                     "\" may not be used in a clocking event expression",
                 Subclause("16.10"));
    }
    lexer.Next();
  }
}

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

static void CaptureInstanceArgs(Lexer& lexer, ModuleItem* item,
                                std::string_view callee) {
  InstanceArgScan scan;
  scan.info.callee = callee;
  lexer.Next();
  while (scan.d > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (!scan.Step(lexer, item)) break;
  }
  item->prop_instance_args.push_back(std::move(scan.info));
}

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

void ScanSystemDefaultValue(Lexer& lexer, DiagEngine& diag, ModuleItem* item,
                            bool clock_default_allowed) {
  auto fn = lexer.Peek().text;
  auto fn_loc = lexer.Peek().loc;
  bool is_inferred = fn == "$inferred_clock" || fn == "$inferred_disable";
  if (is_inferred && !item->prop_formal_inferred.empty()) {
    item->prop_formal_inferred.back() = fn == "$inferred_clock"
                                            ? InferredDefault::kClock
                                            : InferredDefault::kDisable;
  }
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

struct PropertyBodyScanState {
  std::vector<int> case_default_counts;
  bool expect_negated_operand = false;
  bool saw_time_advance = false;
};

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

static void ValidateLiteralNexttimeIndex(Lexer& lexer, DiagEngine& diag) {
  auto index_loc = lexer.Peek().loc;
  auto saved = lexer.SavePos();
  lexer.Next();
  bool negative = false;
  if (LexerCheck(lexer, TokenKind::kMinus)) {
    negative = true;
    lexer.Next();
  }
  bool is_int_literal = LexerCheck(lexer, TokenKind::kIntLiteral);
  lexer.RestorePos(saved);

  if (negative && is_int_literal) {
    diag.Error(index_loc,
               "nexttime index must be a non-negative integer constant "
               "expression",
               Subclause("16.12.10"));
  }
}

struct LiteralRangeBounds {
  SourceLoc loc;
  bool min_negative = false;
  bool min_is_literal = false;
  bool max_negative = false;
  bool max_is_literal = false;
  bool max_is_dollar = false;
  std::string min_text;
  std::string max_text;
};

static LiteralRangeBounds ScanLiteralRange(Lexer& lexer) {
  LiteralRangeBounds r;
  r.loc = lexer.Peek().loc;
  auto saved = lexer.SavePos();
  lexer.Next();
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
    lexer.Next();
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

static void ValidateLiteralAlwaysRange(Lexer& lexer, DiagEngine& diag,
                                       bool strong) {
  auto r = ScanLiteralRange(lexer);
  if (!CheckLiteralRangeBounds(r, diag, "always", Subclause("16.12.11")))
    return;
  if (strong && r.max_is_dollar) {
    diag.Error(r.loc,
               "s_always needs a finite range, so its maximum cannot be `$`",
               Subclause("16.12.11"));
  }
}

static void ValidateLiteralEventuallyRange(Lexer& lexer, DiagEngine& diag,
                                           bool strong) {
  auto r = ScanLiteralRange(lexer);
  if (!CheckLiteralRangeBounds(r, diag, "eventually", Subclause("16.12.13")))
    return;
  if (!strong && r.max_is_dollar) {
    diag.Error(
        r.loc,
        "weak eventually needs a finite range, so its maximum cannot be `$`",
        Subclause("16.12.13"));
  }
}

static void SkipBracketGroup(Lexer& lexer) {
  int depth = 0;
  do {
    if (LexerCheck(lexer, TokenKind::kLBracket)) {
      ++depth;
    } else if (LexerCheck(lexer, TokenKind::kRBracket)) {
      --depth;
    }
    lexer.Next();
  } while (depth > 0 && !lexer.Peek().Is(TokenKind::kEof));
}

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
    ValidateLiteralAlwaysRange(lexer, diag, true);
  else if (is_s_eventually)
    ValidateLiteralEventuallyRange(lexer, diag, true);
  SkipBracketGroup(lexer);
}

static bool ScanOperatorToken(Lexer& lexer, DiagEngine& diag,
                              PropertyBodyScanState& state) {
  if (LexerCheck(lexer, TokenKind::kKwNot) ||
      LexerCheck(lexer, TokenKind::kKwSNexttime) ||
      LexerCheck(lexer, TokenKind::kKwSEventually) ||
      LexerCheck(lexer, TokenKind::kKwSAlways) ||
      LexerCheck(lexer, TokenKind::kKwSUntil) ||
      LexerCheck(lexer, TokenKind::kKwSUntilWith)) {
    ScanStrongPropertyOperator(lexer, diag, state);
    return true;
  }
  if (LexerCheck(lexer, TokenKind::kKwAlways)) {
    state.expect_negated_operand = false;
    lexer.Next();
    if (LexerCheck(lexer, TokenKind::kLBracket))
      ValidateLiteralAlwaysRange(lexer, diag, false);
    return true;
  }
  if (LexerCheck(lexer, TokenKind::kKwEventually)) {
    state.expect_negated_operand = false;
    lexer.Next();
    if (LexerCheck(lexer, TokenKind::kLBracket))
      ValidateLiteralEventuallyRange(lexer, diag, false);
    return true;
  }
  if (LexerCheck(lexer, TokenKind::kHashHash) ||
      LexerCheck(lexer, TokenKind::kPipeEqGt) ||
      LexerCheck(lexer, TokenKind::kKwNexttime)) {
    bool is_nexttime = LexerCheck(lexer, TokenKind::kKwNexttime);
    state.saw_time_advance = true;
    lexer.Next();
    if (is_nexttime && LexerCheck(lexer, TokenKind::kLBracket))
      ValidateLiteralNexttimeIndex(lexer, diag);
    return true;
  }
  return false;
}

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

static void ScanIdentifierToken(Lexer& lexer, DiagEngine& diag,
                                ModuleItem* item,
                                PropertyBodyScanState& state) {
  auto tok = lexer.Next();
  if (LexerCheck(lexer, TokenKind::kLParen)) {
    item->prop_instance_refs.push_back(tok.text);
    if (state.expect_negated_operand) {
      item->prop_negated_instance_refs.push_back(tok.text);
    }
    if (!state.saw_time_advance) {
      item->prop_untimed_instance_refs.push_back(tok.text);
      if (tok.text == item->name) {
        item->prop_has_untimed_self_recursion = true;
      }
    }
    state.expect_negated_operand = false;
    CaptureInstanceArgs(lexer, item, tok.text);
  } else {
    state.expect_negated_operand = false;
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
  if (LexerCheck(lexer, TokenKind::kAt)) {
    ++item->decl_clock_event_count;
    lexer.Next();
    ScanClockEventGroupForLocals(lexer, diag, item);
    return;
  }
  if (ScanCaseDefaultToken(lexer, diag, state)) return;
  if (ScanOperatorToken(lexer, diag, state)) return;
  if (LexerCheck(lexer, TokenKind::kIdentifier)) {
    ScanIdentifierToken(lexer, diag, item, state);
    return;
  }
  if (!LexerCheck(lexer, TokenKind::kLParen))
    state.expect_negated_operand = false;
  lexer.Next();
}

bool Parser::PropertyBodyHasTemporalOperator() {
  auto scan = lexer_.SavePos();
  bool found = false;
  while (!Check(TokenKind::kEof) && !Check(TokenKind::kKwEndproperty)) {
    TokenKind k = CurrentToken().kind;
    if (k == TokenKind::kPipeDashGt || k == TokenKind::kPipeEqGt ||
        k == TokenKind::kHashHash) {
      found = true;
      break;
    }
    Consume();
  }
  lexer_.RestorePos(scan);
  return found;
}

void Parser::CaptureClockedBooleanPropertyBody(ModuleItem* item) {
  if (!Check(TokenKind::kAt) || PropertyBodyHasTemporalOperator()) return;
  auto saved = lexer_.SavePos();
  diag_.PushSuppress();
  Consume();
  std::vector<EventExpr> clock;
  bool ok = Match(TokenKind::kLParen);
  if (ok) {
    clock = ParseEventList();
    ok = Match(TokenKind::kRParen);
  }
  Expr* disable_iff = nullptr;
  if (ok) ok = TryParseDisableIff(disable_iff);
  bool negated = false;
  while (ok && Match(TokenKind::kKwNot)) negated = !negated;
  Expr* boolean =
      ok ? ParserPropertySpecHelpers::ParseExpressionOrDist(*this) : nullptr;
  ok = boolean != nullptr;
  if (ok) Match(TokenKind::kSemicolon);
  ok = ok && Check(TokenKind::kKwEndproperty);
  diag_.PopSuppress();
  lexer_.RestorePos(saved);
  if (!ok) return;
  item->prop_clock = std::move(clock);
  item->prop_body_expr = boolean;
  item->prop_disable_iff = disable_iff;
  item->prop_negated = negated;
}

ModuleItem* Parser::ParsePropertyDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kPropertyDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwProperty, Subclause("16.12"));
  item->name = Expect(TokenKind::kIdentifier, Subclause("16.12")).text;

  if (Match(TokenKind::kLParen)) {
    ParsePropertyPortList(*this, lexer_, diag_, item);
  }

  Expect(TokenKind::kSemicolon, Subclause("16.12"));
  ParserPropertySpecHelpers::RecordAssertionReads(*this, item,
                                                  TokenKind::kKwEndproperty);

  item->decl_has_leading_clock = Check(TokenKind::kAt);

  CaptureClockedBooleanPropertyBody(item);
  ParserPropertySpecHelpers::CapturePropertyTreeBody(*this, item);

  while (AtAssertionVariableDecl(lexer_, known_types_)) {
    HarvestAssertionVariableDecl(item);
  }
  ParserPropertyGrammar::CheckDeclarationBody(*this, false,
                                              TokenKind::kKwEndproperty);
  PropertyBodyScanState scan_state;

  while (!Check(TokenKind::kKwEndproperty) && !AtEnd()) {
    ScanPropertyBodyToken(lexer_, diag_, item, scan_state);
  }
  Expect(TokenKind::kKwEndproperty, Subclause("16.12"));
  MatchEndLabel(item->name);
  return item;
}

}  // namespace delta
