#include <cctype>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
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

static TimeScale DeclaredTimeUnit(const ModuleDecl* mod,
                                  const PackageDecl* pkg) {
  TimeScale scale;
  if (mod != nullptr) {
    scale.unit = mod->time_unit;
    scale.magnitude = mod->time_unit_magnitude;
  } else if (pkg != nullptr) {
    scale.unit = pkg->time_unit;
    scale.magnitude = pkg->time_unit_magnitude;
  }
  return scale;
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
      lit->real_val = TimeLiteralValue(
          lit->text, DeclaredTimeUnit(current_module_, current_package_));
      time_literals_.push_back(
          TimeLiteralSite{lit, current_module_, current_package_});
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

static bool IsSimpleDecimalText(std::string_view text) {
  if (text.empty()) return false;
  for (char c : text) {
    if (!std::isdigit(static_cast<unsigned char>(c)) && c != '_') return false;
  }
  return true;
}

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
