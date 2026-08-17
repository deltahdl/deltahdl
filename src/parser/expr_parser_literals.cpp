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

#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "parser/expr_parser_internal.h"
#include "parser/parser.h"
#include "parser/time_resolve.h"

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

// casting_type allows constant_primary; an integer literal followed by '(expr)
// is a width-cast (the literal is the target width). Otherwise it is just the
// integer literal.
Expr* Parser::ParseIntLiteralPrimary(const Token& tok) {
  auto* lit = MakeLiteral(ExprKind::kIntegerLiteral, tok);
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
