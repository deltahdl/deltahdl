// §5.7 and §5.8: turning a literal's source text into the value it denotes, and
// the checks that reading raises.
//
// §5.7.1 gives an integer literal an optional size and base, so the width and
// the digits have to be pulled back out of the token's text; §5.8 gives a time
// literal a unit suffix, whose scale depends on the `timeunit in force where
// the literal was written. Both are text-to-value conversions rather than
// parsing decisions, which is what separates them from the rest of the
// expression parser: nothing here reads a token beyond the one it was handed.
//
// They stood in src/parser/expr_parser.cpp, which reached 982 lines against the
// 1000 assert-no-oversized-source-files in .github/workflows/deltahdl.yml fails
// at. Parser::MakeLiteral, Parser::WarnSizedOverflow and
// Parser::ParseIntLiteralPrimary are still called from there, being members
// src/parser/parser.h declares.

#include <cctype>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/expr_parser_internal.h"
#include "parser/parser.h"
#include "parser/parser_token_skips.h"

namespace delta {

static uint32_t ExtractLiteralSize(std::string_view text) {
  auto tick = text.find('\'');
  if (tick == std::string_view::npos || tick == 0) return 0;
  uint64_t size = 0;
  for (size_t i = 0; i < tick; ++i) {
    char c = text[i];
    if (c == '_' || c == ' ' || c == '\t') continue;
    if (c < '0' || c > '9') return 0;
    size = size * 10 + (c - '0');
  }
  return static_cast<uint32_t>(size);
}

static bool HasXZDigits(std::string_view text) {
  auto tick = text.find('\'');
  if (tick == std::string_view::npos) return false;
  for (size_t i = tick + 1; i < text.size(); ++i) {
    char c = text[i];
    if (c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?') return true;
  }
  return false;
}

static double ParseRealText(std::string_view text) {
  std::string buf;
  buf.reserve(text.size());
  for (char c : text) {
    if (c != '_') buf.push_back(c);
  }
  return std::strtod(buf.c_str(), nullptr);
}

// Scales a time-literal's real value from the unit named by its suffix into the
// enclosing module's time unit (defaulting to ns when no module is active).
static double ScaleTimeLiteral(double real_val, std::string_view text,
                               TimeUnit current_unit) {
  TimeUnit literal_unit = TimeUnit::kNs;
  auto t = text;
  if (t.size() < 2 || !ParseTimeUnitStr(t.substr(t.size() - 2), literal_unit)) {
    if (!t.empty()) {
      ParseTimeUnitStr(t.substr(t.size() - 1), literal_unit);
    }
  }
  int exp = static_cast<int>(literal_unit) - static_cast<int>(current_unit);
  if (exp != 0) {
    real_val *= std::pow(10.0, exp);
  }
  return real_val;
}

Expr* Parser::MakeLiteral(ExprKind kind, const Token& tok) {
  Consume();
  auto* lit = arena_.Create<Expr>();
  lit->kind = kind;
  lit->text = tok.text;
  lit->range.start = tok.loc;
  if (kind == ExprKind::kIntegerLiteral) {
    lit->int_val = ParseIntText(tok.text);
    WarnSizedOverflow(tok);
  } else if (kind == ExprKind::kUnbasedUnsizedLiteral) {
    if (tok.text.size() >= 2 && tok.text[1] == '1') {
      lit->int_val = ~uint64_t{0};
    }
  } else if (kind == ExprKind::kRealLiteral || kind == ExprKind::kTimeLiteral) {
    lit->real_val = ParseRealText(tok.text);
    if (kind == ExprKind::kTimeLiteral) {
      TimeUnit current_unit =
          current_module_ ? current_module_->time_unit : TimeUnit::kNs;
      lit->real_val = ScaleTimeLiteral(lit->real_val, tok.text, current_unit);
    }
  }
  return lit;
}

void Parser::WarnSizedOverflow(const Token& tok) {
  uint32_t size = ExtractLiteralSize(tok.text);
  if (size == 0) {
    auto tick = tok.text.find('\'');
    if (tick != std::string_view::npos && tick > 0) {
      diag_.Error(tok.loc, "size of integer literal shall be nonzero",
                  Subclause("5.7.1"));
    }
    return;
  }
  if (size >= 64) return;
  if (HasXZDigits(tok.text)) return;
  uint64_t val = ParseIntText(tok.text);
  if (val >= (1ULL << size)) {
    diag_.Warning(tok.loc, "value exceeds size of literal", Subclause("5.7.1"));
  }
}

// Whether `text` is a simple decimal number, the digits and underscores §5.7.1
// composes it of and nothing else -- so no apostrophe, and none of the '.', 'e'
// and unit letters that make a real or a time literal.
static bool IsSimpleDecimalText(std::string_view text) {
  if (text.empty()) return false;
  for (char c : text) {
    if (!std::isdigit(static_cast<unsigned char>(c)) && c != '_') return false;
  }
  return true;
}

// casting_type allows constant_primary; an integer literal followed by '(expr)
// is a width-cast (the literal is the target width). Otherwise it is just the
// integer literal.
//
// §5.7.1 (printed page 77): a based literal is up to three tokens, its size,
// its base and its digits, and §5.4 makes a comment a separator between tokens
// as §5.3's white space is, so `8 /* c */ 'h11` is the one literal 8'h11.
// Lexer::LexNumber reads the size and the based number after it as one token
// across spaces and tabs alone; across a comment or a newline the size arrives
// as a simple decimal token and the rest as an unsized based one, which is the
// pair joined here into the token the lexer would have made of `8 'h11`. The
// joined text is owned by the arena, as the source holds it nowhere. No other
// production puts two integer literals side by side, so the pair is never
// anything else.
//
// §5.7.1's Example 1 lists `4af` as illegal, a simple decimal number being a
// sequence of the digits 0 through 9 and hexadecimal digits going behind a
// base such as 'h. The lexer hands `4af` on as the literal 4 with the
// identifier af against it, the only thing the grammar makes of those
// characters, so a simple decimal literal whose next token is an identifier
// starting where the literal's text ends is the malformed literal it was
// written to be: it is reported under §5.7.1 and the identifier is taken with
// it, so that nothing is left over for the statement to report. Where a name
// is expected instead, the same pair is Parser::ExpectIdentifier's §5.6 report.
Expr* Parser::ParseIntLiteralPrimary(const Token& tok) {
  auto* lit = MakeLiteral(ExprKind::kIntegerLiteral, tok);
  if (IsSimpleDecimalText(tok.text) && Check(TokenKind::kIdentifier) &&
      TokenFollowsDirectly(tok, CurrentToken())) {
    Token letters = Consume();
    std::string_view whole(tok.text.data(),
                           tok.text.size() + letters.text.size());
    diag_.Error(tok.loc,
                "integer literal '" + std::string(whole) +
                    "' shall be decimal digits alone or carry a base such "
                    "as 'h",
                Subclause("5.7.1"));
    return lit;
  }
  if (IsSimpleDecimalText(tok.text) && Check(TokenKind::kIntLiteral) &&
      !CurrentToken().text.empty() && CurrentToken().text.front() == '\'') {
    Token based = Consume();
    auto* joined = arena_.Create<std::string>(std::string(tok.text) + " " +
                                              std::string(based.text));
    Token whole = tok;
    whole.text = *joined;
    lit->text = whole.text;
    lit->int_val = ParseIntText(whole.text);
    WarnSizedOverflow(whole);
    return lit;
  }
  if (!Check(TokenKind::kApostrophe)) return lit;
  auto saved = lexer_.SavePos();
  Consume();
  if (!Check(TokenKind::kLParen)) {
    lexer_.RestorePos(saved);
    return lit;
  }
  Consume();
  auto* value = ParseExpr();
  auto* cast = MakeNodeCast(arena_, lit, value);
  Expect(TokenKind::kRParen, Subclause("6.24.1"));
  return cast;
}
}  // namespace delta
