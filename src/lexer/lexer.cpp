#include "lexer/lexer.h"

#include <cctype>

#include "lexer/keywords.h"

namespace delta {

Lexer::Lexer(std::string_view source, uint32_t file_id, DiagEngine& diag)
    : source_(source), file_id_(file_id), diag_(diag) {}

char Lexer::current() const {
  if (at_end()) {
    return '\0';
  }
  return source_[pos_];
}

char Lexer::peek_char() const {
  if (pos_ + 1 >= source_.size()) {
    return '\0';
  }
  return source_[pos_ + 1];
}

void Lexer::advance() {
  if (at_end()) {
    return;
  }
  if (source_[pos_] == '\n') {
    ++line_;
    column_ = 1;
  } else {
    ++column_;
  }
  ++pos_;
}

bool Lexer::at_end() const { return pos_ >= source_.size(); }

SourceLoc Lexer::make_loc() const { return {file_id_, line_, column_}; }

// ---------------------------------------------------------------------------
// Whitespace and comments
// ---------------------------------------------------------------------------

void Lexer::skip_line_comment() {
  while (!at_end() && current() != '\n') {
    advance();
  }
}

void Lexer::skip_block_comment() {
  // Caller has already consumed '/' and '*'.
  while (!at_end()) {
    if (current() == '*' && peek_char() == '/') {
      advance();
      advance();
      return;
    }
    advance();
  }
}

void Lexer::skip_whitespace_and_comments() {
  while (!at_end()) {
    if (std::isspace(static_cast<unsigned char>(current()))) {
      advance();
      continue;
    }
    if (current() == '/' && peek_char() == '/') {
      skip_line_comment();
      continue;
    }
    if (current() == '/' && peek_char() == '*') {
      advance();  // skip '/'
      advance();  // skip '*'
      skip_block_comment();
      continue;
    }
    break;
  }
}

// ---------------------------------------------------------------------------
// Token construction
// ---------------------------------------------------------------------------

Token Lexer::make_token(TokenKind kind, SourceLoc loc) const {
  Token tok;
  tok.kind = kind;
  tok.loc = loc;
  return tok;
}

Token Lexer::make_op(TokenKind kind, SourceLoc loc, uint32_t start) {
  Token tok;
  tok.kind = kind;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

// ---------------------------------------------------------------------------
// Top-level dispatch
// ---------------------------------------------------------------------------

Token Lexer::next() {
  if (has_peeked_) {
    has_peeked_ = false;
    return peeked_;
  }
  skip_whitespace_and_comments();
  if (at_end()) {
    return make_token(TokenKind::Eof, make_loc());
  }
  char c = current();
  if (c == '$') {
    return lex_system_identifier();
  }
  if (c == '\\') {
    return lex_escaped_identifier();
  }
  if (c == '"') {
    return lex_string_literal();
  }
  if (std::isalpha(static_cast<unsigned char>(c)) || c == '_') {
    return lex_identifier();
  }
  if (std::isdigit(static_cast<unsigned char>(c))) {
    return lex_number();
  }
  if (c == '\'' && !std::isalpha(static_cast<unsigned char>(peek_char()))) {
    return lex_number();
  }
  return lex_operator();
}

Token Lexer::peek() {
  if (!has_peeked_) {
    peeked_ = next();
    has_peeked_ = true;
  }
  return peeked_;
}

// ---------------------------------------------------------------------------
// Identifiers
// ---------------------------------------------------------------------------

Token Lexer::lex_identifier() {
  auto loc = make_loc();
  uint32_t start = pos_;
  while (!at_end() && (std::isalnum(static_cast<unsigned char>(current())) ||
                       current() == '_' || current() == '$')) {
    advance();
  }
  std::string_view text = source_.substr(start, pos_ - start);
  auto kw = lookup_keyword(text);
  Token tok;
  tok.kind = kw.value_or(TokenKind::Identifier);
  tok.loc = loc;
  tok.text = text;
  return tok;
}

// ---------------------------------------------------------------------------
// Numbers
// ---------------------------------------------------------------------------

Token Lexer::lex_unbased_unsized(SourceLoc loc, uint32_t start) {
  advance();  // skip '
  if (!at_end()) {
    advance();  // value character
  }
  Token tok;
  tok.kind = TokenKind::UnbasedUnsizedLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

Token Lexer::lex_based_number(SourceLoc loc, uint32_t start) {
  advance();  // skip '
  if (!at_end()) {
    advance();  // base letter
  }
  while (!at_end() &&
         (std::isxdigit(static_cast<unsigned char>(current())) ||
          current() == '_' || current() == 'x' || current() == 'z' ||
          current() == 'X' || current() == 'Z' || current() == '?')) {
    advance();
  }
  Token tok;
  tok.kind = TokenKind::IntLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

void Lexer::lex_fractional_part() {
  if (at_end() || current() != '.') return;
  if (!std::isdigit(static_cast<unsigned char>(peek_char()))) return;
  advance();
  while (!at_end() && (std::isdigit(static_cast<unsigned char>(current())) ||
                       current() == '_')) {
    advance();
  }
}

void Lexer::lex_exponent_part() {
  if (at_end()) return;
  if (current() != 'e' && current() != 'E') return;
  advance();
  if (!at_end() && (current() == '+' || current() == '-')) {
    advance();
  }
  while (!at_end() && std::isdigit(static_cast<unsigned char>(current()))) {
    advance();
  }
}

void Lexer::lex_real_suffix() {
  lex_fractional_part();
  lex_exponent_part();
}

Token Lexer::lex_number() {
  auto loc = make_loc();
  uint32_t start = pos_;

  if (current() == '\'') {
    return lex_unbased_unsized(loc, start);
  }

  // Decimal digits
  while (!at_end() && (std::isdigit(static_cast<unsigned char>(current())) ||
                       current() == '_')) {
    advance();
  }

  // Check for base specifier: 'h, 'b, 'o, 'd
  if (!at_end() && current() == '\'') {
    return lex_based_number(loc, start);
  }

  // Check for real literal (decimal point or exponent)
  lex_real_suffix();

  Token tok;
  tok.kind = TokenKind::IntLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

// ---------------------------------------------------------------------------
// String / system / escaped identifiers
// ---------------------------------------------------------------------------

Token Lexer::lex_string_literal() {
  auto loc = make_loc();
  uint32_t start = pos_;
  advance();  // skip opening "
  while (!at_end() && current() != '"') {
    if (current() == '\\') {
      advance();
    }
    advance();
  }
  if (!at_end()) {
    advance();  // skip closing "
  }
  Token tok;
  tok.kind = TokenKind::StringLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

Token Lexer::lex_system_identifier() {
  auto loc = make_loc();
  uint32_t start = pos_;
  advance();  // skip $
  while (!at_end() && (std::isalnum(static_cast<unsigned char>(current())) ||
                       current() == '_')) {
    advance();
  }
  Token tok;
  tok.kind = TokenKind::SystemIdentifier;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

Token Lexer::lex_escaped_identifier() {
  auto loc = make_loc();
  uint32_t start = pos_;
  advance();  // skip backslash
  while (!at_end() && !std::isspace(static_cast<unsigned char>(current()))) {
    advance();
  }
  Token tok;
  tok.kind = TokenKind::EscapedIdentifier;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

// ---------------------------------------------------------------------------
// Operator sub-helpers
// ---------------------------------------------------------------------------

Token Lexer::lex_op_tilde(SourceLoc loc, uint32_t start) {
  if (!at_end() && current() == '&') {
    advance();
    return make_op(TokenKind::TildeAmp, loc, start);
  }
  if (!at_end() && current() == '|') {
    advance();
    return make_op(TokenKind::TildePipe, loc, start);
  }
  if (!at_end() && current() == '^') {
    advance();
    return make_op(TokenKind::TildeCaret, loc, start);
  }
  return make_op(TokenKind::Tilde, loc, start);
}

Token Lexer::lex_op_plus(SourceLoc loc, uint32_t start) {
  if (!at_end() && current() == '+') {
    advance();
    return make_op(TokenKind::PlusPlus, loc, start);
  }
  if (!at_end() && current() == '=') {
    advance();
    return make_op(TokenKind::PlusEq, loc, start);
  }
  return make_op(TokenKind::Plus, loc, start);
}

Token Lexer::lex_op_minus(SourceLoc loc, uint32_t start) {
  if (!at_end() && current() == '-') {
    advance();
    return make_op(TokenKind::MinusMinus, loc, start);
  }
  if (!at_end() && current() == '=') {
    advance();
    return make_op(TokenKind::MinusEq, loc, start);
  }
  if (!at_end() && current() == '>') {
    advance();
    if (!at_end() && current() == '>') {
      advance();
      return make_op(TokenKind::DashGtGt, loc, start);
    }
    return make_op(TokenKind::Arrow, loc, start);
  }
  return make_op(TokenKind::Minus, loc, start);
}

Token Lexer::lex_op_star(SourceLoc loc, uint32_t start) {
  if (!at_end() && current() == '*') {
    advance();
    return make_op(TokenKind::Power, loc, start);
  }
  if (!at_end() && current() == '=') {
    advance();
    return make_op(TokenKind::StarEq, loc, start);
  }
  if (!at_end() && current() == '>') {
    advance();
    return make_op(TokenKind::StarGt, loc, start);
  }
  return make_op(TokenKind::Star, loc, start);
}

Token Lexer::lex_op_caret(SourceLoc loc, uint32_t start) {
  if (!at_end() && current() == '~') {
    advance();
    return make_op(TokenKind::CaretTilde, loc, start);
  }
  if (!at_end() && current() == '=') {
    advance();
    return make_op(TokenKind::CaretEq, loc, start);
  }
  return make_op(TokenKind::Caret, loc, start);
}

Token Lexer::lex_op_amp(SourceLoc loc, uint32_t start) {
  if (!at_end() && current() == '&') {
    advance();
    if (!at_end() && current() == '&') {
      advance();
      return make_op(TokenKind::AmpAmpAmp, loc, start);
    }
    return make_op(TokenKind::AmpAmp, loc, start);
  }
  if (!at_end() && current() == '=') {
    advance();
    return make_op(TokenKind::AmpEq, loc, start);
  }
  return make_op(TokenKind::Amp, loc, start);
}

Token Lexer::lex_op_pipe(SourceLoc loc, uint32_t start) {
  if (!at_end() && current() == '|') {
    advance();
    return make_op(TokenKind::PipePipe, loc, start);
  }
  if (!at_end() && current() == '=') {
    advance();
    if (!at_end() && current() == '>') {
      advance();
      return make_op(TokenKind::PipeEqGt, loc, start);
    }
    return make_op(TokenKind::PipeEq, loc, start);
  }
  if (!at_end() && current() == '-' && peek_char() == '>') {
    advance();
    advance();
    return make_op(TokenKind::PipeDashGt, loc, start);
  }
  return make_op(TokenKind::Pipe, loc, start);
}

Token Lexer::lex_op_bang(SourceLoc loc, uint32_t start) {
  if (!at_end() && current() == '=') {
    advance();
    if (!at_end() && current() == '=') {
      advance();
      return make_op(TokenKind::BangEqEq, loc, start);
    }
    if (!at_end() && current() == '?') {
      advance();
      return make_op(TokenKind::BangEqQuestion, loc, start);
    }
    return make_op(TokenKind::BangEq, loc, start);
  }
  return make_op(TokenKind::Bang, loc, start);
}

Token Lexer::lex_op_eq(SourceLoc loc, uint32_t start) {
  if (!at_end() && current() == '=') {
    advance();
    if (!at_end() && current() == '=') {
      advance();
      return make_op(TokenKind::EqEqEq, loc, start);
    }
    if (!at_end() && current() == '?') {
      advance();
      return make_op(TokenKind::EqEqQuestion, loc, start);
    }
    return make_op(TokenKind::EqEq, loc, start);
  }
  if (!at_end() && current() == '>') {
    advance();
    return make_op(TokenKind::EqGt, loc, start);
  }
  return make_op(TokenKind::Eq, loc, start);
}

Token Lexer::lex_op_hash(SourceLoc loc, uint32_t start) {
  if (!at_end() && current() == '#') {
    advance();
    return make_op(TokenKind::HashHash, loc, start);
  }
  return make_op(TokenKind::Hash, loc, start);
}

Token Lexer::lex_op_dot(SourceLoc loc, uint32_t start) {
  if (!at_end() && current() == '*') {
    advance();
    return make_op(TokenKind::DotStar, loc, start);
  }
  return make_op(TokenKind::Dot, loc, start);
}

Token Lexer::lex_op_colon(SourceLoc loc, uint32_t start) {
  if (!at_end() && current() == ':') {
    advance();
    return make_op(TokenKind::ColonColon, loc, start);
  }
  return make_op(TokenKind::Colon, loc, start);
}

Token Lexer::lex_op_at(SourceLoc loc, uint32_t start) {
  if (!at_end() && current() == '@') {
    advance();
    return make_op(TokenKind::AtAt, loc, start);
  }
  return make_op(TokenKind::At, loc, start);
}

Token Lexer::lex_op_slash(SourceLoc loc, uint32_t start) {
  if (!at_end() && current() == '=') {
    advance();
    return make_op(TokenKind::SlashEq, loc, start);
  }
  return make_op(TokenKind::Slash, loc, start);
}

Token Lexer::lex_op_percent(SourceLoc loc, uint32_t start) {
  if (!at_end() && current() == '=') {
    advance();
    return make_op(TokenKind::PercentEq, loc, start);
  }
  return make_op(TokenKind::Percent, loc, start);
}

Token Lexer::lex_angle_left(SourceLoc loc, uint32_t start) {
  if (at_end()) {
    return make_op(TokenKind::Lt, loc, start);
  }
  if (current() == '=') {
    advance();
    return make_op(TokenKind::LtEq, loc, start);
  }
  if (current() != '<') {
    return make_op(TokenKind::Lt, loc, start);
  }
  advance();  // second <
  if (!at_end() && current() == '<') {
    advance();
    if (!at_end() && current() == '=') {
      advance();
      return make_op(TokenKind::LtLtLtEq, loc, start);
    }
    return make_op(TokenKind::LtLtLt, loc, start);
  }
  if (!at_end() && current() == '=') {
    advance();
    return make_op(TokenKind::LtLtEq, loc, start);
  }
  return make_op(TokenKind::LtLt, loc, start);
}

Token Lexer::lex_angle_right(SourceLoc loc, uint32_t start) {
  if (at_end()) {
    return make_op(TokenKind::Gt, loc, start);
  }
  if (current() == '=') {
    advance();
    return make_op(TokenKind::GtEq, loc, start);
  }
  if (current() != '>') {
    return make_op(TokenKind::Gt, loc, start);
  }
  advance();  // second >
  if (!at_end() && current() == '>') {
    advance();
    if (!at_end() && current() == '=') {
      advance();
      return make_op(TokenKind::GtGtGtEq, loc, start);
    }
    return make_op(TokenKind::GtGtGt, loc, start);
  }
  if (!at_end() && current() == '=') {
    advance();
    return make_op(TokenKind::GtGtEq, loc, start);
  }
  return make_op(TokenKind::GtGt, loc, start);
}

// ---------------------------------------------------------------------------
// Main operator dispatch
// ---------------------------------------------------------------------------

Token Lexer::lex_operator() {
  auto loc = make_loc();
  uint32_t start = pos_;
  char c = current();
  advance();

  switch (c) {
    case '(':
      return make_op(TokenKind::LParen, loc, start);
    case ')':
      return make_op(TokenKind::RParen, loc, start);
    case '[':
      return make_op(TokenKind::LBracket, loc, start);
    case ']':
      return make_op(TokenKind::RBracket, loc, start);
    case '{':
      return make_op(TokenKind::LBrace, loc, start);
    case '}':
      return make_op(TokenKind::RBrace, loc, start);
    case ';':
      return make_op(TokenKind::Semicolon, loc, start);
    case ',':
      return make_op(TokenKind::Comma, loc, start);
    case '?':
      return make_op(TokenKind::Question, loc, start);
    case '~':
      return lex_op_tilde(loc, start);
    case '+':
      return lex_op_plus(loc, start);
    case '-':
      return lex_op_minus(loc, start);
    case '*':
      return lex_op_star(loc, start);
    case '/':
      return lex_op_slash(loc, start);
    case '%':
      return lex_op_percent(loc, start);
    case '^':
      return lex_op_caret(loc, start);
    case '&':
      return lex_op_amp(loc, start);
    case '|':
      return lex_op_pipe(loc, start);
    case '!':
      return lex_op_bang(loc, start);
    case '=':
      return lex_op_eq(loc, start);
    case '#':
      return lex_op_hash(loc, start);
    case '.':
      return lex_op_dot(loc, start);
    case ':':
      return lex_op_colon(loc, start);
    case '@':
      return lex_op_at(loc, start);
    case '<':
      return lex_angle_left(loc, start);
    case '>':
      return lex_angle_right(loc, start);
    default:
      break;
  }

  diag_.error(loc, std::string("unexpected character '") + c + "'");
  Token tok;
  tok.kind = TokenKind::Error;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

// ---------------------------------------------------------------------------
// Bulk lexing
// ---------------------------------------------------------------------------

std::vector<Token> Lexer::lex_all() {
  std::vector<Token> tokens;
  while (true) {
    auto tok = next();
    tokens.push_back(tok);
    if (tok.is_eof()) {
      break;
    }
  }
  return tokens;
}

}  // namespace delta
