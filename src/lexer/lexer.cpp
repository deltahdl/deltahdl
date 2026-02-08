#include "lexer/lexer.h"

#include <cctype>

#include "lexer/keywords.h"

namespace delta {

Lexer::Lexer(std::string_view source, uint32_t file_id, DiagEngine& diag)
    : source_(source), file_id_(file_id), diag_(diag) {}

char Lexer::Current() const {
  if (AtEnd()) {
    return '\0';
  }
  return source_[pos_];
}

char Lexer::PeekChar() const {
  if (pos_ + 1 >= source_.size()) {
    return '\0';
  }
  return source_[pos_ + 1];
}

void Lexer::Advance() {
  if (AtEnd()) {
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

bool Lexer::AtEnd() const { return pos_ >= source_.size(); }

SourceLoc Lexer::MakeLoc() const { return {file_id_, line_, column_}; }

// ---------------------------------------------------------------------------
// Whitespace and comments
// ---------------------------------------------------------------------------

void Lexer::SkipLineComment() {
  while (!AtEnd() && Current() != '\n') {
    Advance();
  }
}

void Lexer::SkipBlockComment() {
  // Caller has already consumed '/' and '*'.
  while (!AtEnd()) {
    if (Current() == '*' && PeekChar() == '/') {
      Advance();
      Advance();
      return;
    }
    Advance();
  }
}

void Lexer::SkipWhitespaceAndComments() {
  while (!AtEnd()) {
    if (std::isspace(static_cast<unsigned char>(Current()))) {
      Advance();
      continue;
    }
    if (Current() == '/' && PeekChar() == '/') {
      SkipLineComment();
      continue;
    }
    if (Current() == '/' && PeekChar() == '*') {
      Advance();  // skip '/'
      Advance();  // skip '*'
      SkipBlockComment();
      continue;
    }
    break;
  }
}

// ---------------------------------------------------------------------------
// Token construction
// ---------------------------------------------------------------------------

Token Lexer::MakeToken(TokenKind kind, SourceLoc loc) const {
  Token tok;
  tok.kind = kind;
  tok.loc = loc;
  return tok;
}

Token Lexer::MakeOp(TokenKind kind, SourceLoc loc, uint32_t start) {
  Token tok;
  tok.kind = kind;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

// ---------------------------------------------------------------------------
// Top-level dispatch
// ---------------------------------------------------------------------------

Token Lexer::Next() {
  if (has_peeked_) {
    has_peeked_ = false;
    return peeked_;
  }
  SkipWhitespaceAndComments();
  if (AtEnd()) {
    return MakeToken(TokenKind::kEof, MakeLoc());
  }
  char c = Current();
  if (c == '$') {
    return LexSystemIdentifier();
  }
  if (c == '\\') {
    return LexEscapedIdentifier();
  }
  if (c == '"') {
    return LexStringLiteral();
  }
  if (std::isalpha(static_cast<unsigned char>(c)) || c == '_') {
    return LexIdentifier();
  }
  if (std::isdigit(static_cast<unsigned char>(c))) {
    return LexNumber();
  }
  if (c == '\'' && !std::isalpha(static_cast<unsigned char>(PeekChar()))) {
    return LexNumber();
  }
  return LexOperator();
}

Token Lexer::Peek() {
  if (!has_peeked_) {
    peeked_ = Next();
    has_peeked_ = true;
  }
  return peeked_;
}

// ---------------------------------------------------------------------------
// Identifiers
// ---------------------------------------------------------------------------

Token Lexer::LexIdentifier() {
  auto loc = MakeLoc();
  uint32_t start = pos_;
  while (!AtEnd() && (std::isalnum(static_cast<unsigned char>(Current())) ||
                      Current() == '_' || Current() == '$')) {
    Advance();
  }
  std::string_view text = source_.substr(start, pos_ - start);
  auto kw = LookupKeyword(text);
  Token tok;
  tok.kind = kw.value_or(TokenKind::kIdentifier);
  tok.loc = loc;
  tok.text = text;
  return tok;
}

// ---------------------------------------------------------------------------
// Numbers
// ---------------------------------------------------------------------------

Token Lexer::LexUnbasedUnsized(SourceLoc loc, uint32_t start) {
  Advance();  // skip '
  if (!AtEnd()) {
    Advance();  // value character
  }
  Token tok;
  tok.kind = TokenKind::kUnbasedUnsizedLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

Token Lexer::LexBasedNumber(SourceLoc loc, uint32_t start) {
  Advance();  // skip '
  if (!AtEnd()) {
    Advance();  // base letter
  }
  while (!AtEnd() &&
         (std::isxdigit(static_cast<unsigned char>(Current())) ||
          Current() == '_' || Current() == 'x' || Current() == 'z' ||
          Current() == 'X' || Current() == 'Z' || Current() == '?')) {
    Advance();
  }
  Token tok;
  tok.kind = TokenKind::kIntLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

void Lexer::LexFractionalPart() {
  if (AtEnd() || Current() != '.') return;
  if (!std::isdigit(static_cast<unsigned char>(PeekChar()))) return;
  Advance();
  while (!AtEnd() && (std::isdigit(static_cast<unsigned char>(Current())) ||
                      Current() == '_')) {
    Advance();
  }
}

void Lexer::LexExponentPart() {
  if (AtEnd()) return;
  if (Current() != 'e' && Current() != 'E') return;
  Advance();
  if (!AtEnd() && (Current() == '+' || Current() == '-')) {
    Advance();
  }
  while (!AtEnd() && std::isdigit(static_cast<unsigned char>(Current()))) {
    Advance();
  }
}

void Lexer::LexRealSuffix() {
  LexFractionalPart();
  LexExponentPart();
}

bool Lexer::TryLexTimeSuffix() {
  if (AtEnd()) return false;
  uint32_t save = pos_;
  // Two-character suffixes first: ms, us, ns, ps, fs.
  if (pos_ + 1 < source_.size()) {
    char c0 = source_[pos_];
    char c1 = source_[pos_ + 1];
    bool is_two_char =
        (c0 == 'm' || c0 == 'u' || c0 == 'n' || c0 == 'p' || c0 == 'f') &&
        c1 == 's';
    if (is_two_char) {
      Advance();
      Advance();
      return true;
    }
  }
  // Single character: just 's'.
  if (source_[pos_] == 's') {
    Advance();
    return true;
  }
  pos_ = save;
  return false;
}

Token Lexer::LexNumber() {
  auto loc = MakeLoc();
  uint32_t start = pos_;

  if (Current() == '\'') {
    return LexUnbasedUnsized(loc, start);
  }

  // Decimal digits
  while (!AtEnd() && (std::isdigit(static_cast<unsigned char>(Current())) ||
                      Current() == '_')) {
    Advance();
  }

  // Check for base specifier: 'h, 'b, 'o, 'd
  if (!AtEnd() && Current() == '\'') {
    return LexBasedNumber(loc, start);
  }

  // Check for real literal (decimal point or exponent)
  uint32_t before_real = pos_;
  LexRealSuffix();
  bool is_real = (pos_ != before_real);

  // Check for time suffix (s, ms, us, ns, ps, fs).
  bool is_time = TryLexTimeSuffix();

  Token tok;
  tok.kind = is_time   ? TokenKind::kTimeLiteral
             : is_real ? TokenKind::kRealLiteral
                       : TokenKind::kIntLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

// ---------------------------------------------------------------------------
// String / system / escaped identifiers
// ---------------------------------------------------------------------------

Token Lexer::LexStringLiteral() {
  auto loc = MakeLoc();
  uint32_t start = pos_;
  Advance();  // skip opening "
  while (!AtEnd() && Current() != '"') {
    if (Current() == '\\') {
      Advance();
    }
    Advance();
  }
  if (!AtEnd()) {
    Advance();  // skip closing "
  }
  Token tok;
  tok.kind = TokenKind::kStringLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

Token Lexer::LexSystemIdentifier() {
  auto loc = MakeLoc();
  uint32_t start = pos_;
  Advance();  // skip $
  while (!AtEnd() && (std::isalnum(static_cast<unsigned char>(Current())) ||
                      Current() == '_')) {
    Advance();
  }
  Token tok;
  tok.kind = TokenKind::kSystemIdentifier;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

Token Lexer::LexEscapedIdentifier() {
  auto loc = MakeLoc();
  uint32_t start = pos_;
  Advance();  // skip backslash
  while (!AtEnd() && !std::isspace(static_cast<unsigned char>(Current()))) {
    Advance();
  }
  Token tok;
  tok.kind = TokenKind::kEscapedIdentifier;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

// ---------------------------------------------------------------------------
// Operator sub-helpers
// ---------------------------------------------------------------------------

Token Lexer::LexOpTilde(SourceLoc loc, uint32_t start) {
  if (!AtEnd() && Current() == '&') {
    Advance();
    return MakeOp(TokenKind::kTildeAmp, loc, start);
  }
  if (!AtEnd() && Current() == '|') {
    Advance();
    return MakeOp(TokenKind::kTildePipe, loc, start);
  }
  if (!AtEnd() && Current() == '^') {
    Advance();
    return MakeOp(TokenKind::kTildeCaret, loc, start);
  }
  return MakeOp(TokenKind::kTilde, loc, start);
}

Token Lexer::LexOpPlus(SourceLoc loc, uint32_t start) {
  if (!AtEnd() && Current() == '+') {
    Advance();
    return MakeOp(TokenKind::kPlusPlus, loc, start);
  }
  if (!AtEnd() && Current() == '=') {
    Advance();
    return MakeOp(TokenKind::kPlusEq, loc, start);
  }
  return MakeOp(TokenKind::kPlus, loc, start);
}

Token Lexer::LexOpMinus(SourceLoc loc, uint32_t start) {
  if (!AtEnd() && Current() == '-') {
    Advance();
    return MakeOp(TokenKind::kMinusMinus, loc, start);
  }
  if (!AtEnd() && Current() == '=') {
    Advance();
    return MakeOp(TokenKind::kMinusEq, loc, start);
  }
  if (!AtEnd() && Current() == '>') {
    Advance();
    if (!AtEnd() && Current() == '>') {
      Advance();
      return MakeOp(TokenKind::kDashGtGt, loc, start);
    }
    return MakeOp(TokenKind::kArrow, loc, start);
  }
  return MakeOp(TokenKind::kMinus, loc, start);
}

Token Lexer::LexOpStar(SourceLoc loc, uint32_t start) {
  if (!AtEnd() && Current() == '*') {
    Advance();
    return MakeOp(TokenKind::kPower, loc, start);
  }
  if (!AtEnd() && Current() == '=') {
    Advance();
    return MakeOp(TokenKind::kStarEq, loc, start);
  }
  if (!AtEnd() && Current() == '>') {
    Advance();
    return MakeOp(TokenKind::kStarGt, loc, start);
  }
  return MakeOp(TokenKind::kStar, loc, start);
}

Token Lexer::LexOpCaret(SourceLoc loc, uint32_t start) {
  if (!AtEnd() && Current() == '~') {
    Advance();
    return MakeOp(TokenKind::kCaretTilde, loc, start);
  }
  if (!AtEnd() && Current() == '=') {
    Advance();
    return MakeOp(TokenKind::kCaretEq, loc, start);
  }
  return MakeOp(TokenKind::kCaret, loc, start);
}

Token Lexer::LexOpAmp(SourceLoc loc, uint32_t start) {
  if (!AtEnd() && Current() == '&') {
    Advance();
    if (!AtEnd() && Current() == '&') {
      Advance();
      return MakeOp(TokenKind::kAmpAmpAmp, loc, start);
    }
    return MakeOp(TokenKind::kAmpAmp, loc, start);
  }
  if (!AtEnd() && Current() == '=') {
    Advance();
    return MakeOp(TokenKind::kAmpEq, loc, start);
  }
  return MakeOp(TokenKind::kAmp, loc, start);
}

Token Lexer::LexOpPipe(SourceLoc loc, uint32_t start) {
  if (!AtEnd() && Current() == '|') {
    Advance();
    return MakeOp(TokenKind::kPipePipe, loc, start);
  }
  if (!AtEnd() && Current() == '=') {
    Advance();
    if (!AtEnd() && Current() == '>') {
      Advance();
      return MakeOp(TokenKind::kPipeEqGt, loc, start);
    }
    return MakeOp(TokenKind::kPipeEq, loc, start);
  }
  if (!AtEnd() && Current() == '-' && PeekChar() == '>') {
    Advance();
    Advance();
    return MakeOp(TokenKind::kPipeDashGt, loc, start);
  }
  return MakeOp(TokenKind::kPipe, loc, start);
}

Token Lexer::LexOpBang(SourceLoc loc, uint32_t start) {
  if (!AtEnd() && Current() == '=') {
    Advance();
    if (!AtEnd() && Current() == '=') {
      Advance();
      return MakeOp(TokenKind::kBangEqEq, loc, start);
    }
    if (!AtEnd() && Current() == '?') {
      Advance();
      return MakeOp(TokenKind::kBangEqQuestion, loc, start);
    }
    return MakeOp(TokenKind::kBangEq, loc, start);
  }
  return MakeOp(TokenKind::kBang, loc, start);
}

Token Lexer::LexOpEq(SourceLoc loc, uint32_t start) {
  if (!AtEnd() && Current() == '=') {
    Advance();
    if (!AtEnd() && Current() == '=') {
      Advance();
      return MakeOp(TokenKind::kEqEqEq, loc, start);
    }
    if (!AtEnd() && Current() == '?') {
      Advance();
      return MakeOp(TokenKind::kEqEqQuestion, loc, start);
    }
    return MakeOp(TokenKind::kEqEq, loc, start);
  }
  if (!AtEnd() && Current() == '>') {
    Advance();
    return MakeOp(TokenKind::kEqGt, loc, start);
  }
  return MakeOp(TokenKind::kEq, loc, start);
}

Token Lexer::LexOpHash(SourceLoc loc, uint32_t start) {
  if (!AtEnd() && Current() == '#') {
    Advance();
    return MakeOp(TokenKind::kHashHash, loc, start);
  }
  return MakeOp(TokenKind::kHash, loc, start);
}

Token Lexer::LexOpDot(SourceLoc loc, uint32_t start) {
  if (!AtEnd() && Current() == '*') {
    Advance();
    return MakeOp(TokenKind::kDotStar, loc, start);
  }
  return MakeOp(TokenKind::kDot, loc, start);
}

Token Lexer::LexOpColon(SourceLoc loc, uint32_t start) {
  if (!AtEnd() && Current() == ':') {
    Advance();
    return MakeOp(TokenKind::kColonColon, loc, start);
  }
  return MakeOp(TokenKind::kColon, loc, start);
}

Token Lexer::LexOpAt(SourceLoc loc, uint32_t start) {
  if (!AtEnd() && Current() == '@') {
    Advance();
    return MakeOp(TokenKind::kAtAt, loc, start);
  }
  return MakeOp(TokenKind::kAt, loc, start);
}

Token Lexer::LexOpSlash(SourceLoc loc, uint32_t start) {
  if (!AtEnd() && Current() == '=') {
    Advance();
    return MakeOp(TokenKind::kSlashEq, loc, start);
  }
  return MakeOp(TokenKind::kSlash, loc, start);
}

Token Lexer::LexOpPercent(SourceLoc loc, uint32_t start) {
  if (!AtEnd() && Current() == '=') {
    Advance();
    return MakeOp(TokenKind::kPercentEq, loc, start);
  }
  return MakeOp(TokenKind::kPercent, loc, start);
}

Token Lexer::LexAngleLeft(SourceLoc loc, uint32_t start) {
  if (AtEnd()) {
    return MakeOp(TokenKind::kLt, loc, start);
  }
  if (Current() == '=') {
    Advance();
    return MakeOp(TokenKind::kLtEq, loc, start);
  }
  if (Current() != '<') {
    return MakeOp(TokenKind::kLt, loc, start);
  }
  Advance();  // second <
  if (!AtEnd() && Current() == '<') {
    Advance();
    if (!AtEnd() && Current() == '=') {
      Advance();
      return MakeOp(TokenKind::kLtLtLtEq, loc, start);
    }
    return MakeOp(TokenKind::kLtLtLt, loc, start);
  }
  if (!AtEnd() && Current() == '=') {
    Advance();
    return MakeOp(TokenKind::kLtLtEq, loc, start);
  }
  return MakeOp(TokenKind::kLtLt, loc, start);
}

Token Lexer::LexAngleRight(SourceLoc loc, uint32_t start) {
  if (AtEnd()) {
    return MakeOp(TokenKind::kGt, loc, start);
  }
  if (Current() == '=') {
    Advance();
    return MakeOp(TokenKind::kGtEq, loc, start);
  }
  if (Current() != '>') {
    return MakeOp(TokenKind::kGt, loc, start);
  }
  Advance();  // second >
  if (!AtEnd() && Current() == '>') {
    Advance();
    if (!AtEnd() && Current() == '=') {
      Advance();
      return MakeOp(TokenKind::kGtGtGtEq, loc, start);
    }
    return MakeOp(TokenKind::kGtGtGt, loc, start);
  }
  if (!AtEnd() && Current() == '=') {
    Advance();
    return MakeOp(TokenKind::kGtGtEq, loc, start);
  }
  return MakeOp(TokenKind::kGtGt, loc, start);
}

// ---------------------------------------------------------------------------
// Main operator dispatch
// ---------------------------------------------------------------------------

Token Lexer::LexOperator() {
  auto loc = MakeLoc();
  uint32_t start = pos_;
  char c = Current();
  Advance();

  switch (c) {
    case '(':
      return MakeOp(TokenKind::kLParen, loc, start);
    case ')':
      return MakeOp(TokenKind::kRParen, loc, start);
    case '[':
      return MakeOp(TokenKind::kLBracket, loc, start);
    case ']':
      return MakeOp(TokenKind::kRBracket, loc, start);
    case '{':
      return MakeOp(TokenKind::kLBrace, loc, start);
    case '}':
      return MakeOp(TokenKind::kRBrace, loc, start);
    case ';':
      return MakeOp(TokenKind::kSemicolon, loc, start);
    case ',':
      return MakeOp(TokenKind::kComma, loc, start);
    case '?':
      return MakeOp(TokenKind::kQuestion, loc, start);
    case '~':
      return LexOpTilde(loc, start);
    case '+':
      return LexOpPlus(loc, start);
    case '-':
      return LexOpMinus(loc, start);
    case '*':
      return LexOpStar(loc, start);
    case '/':
      return LexOpSlash(loc, start);
    case '%':
      return LexOpPercent(loc, start);
    case '^':
      return LexOpCaret(loc, start);
    case '&':
      return LexOpAmp(loc, start);
    case '|':
      return LexOpPipe(loc, start);
    case '!':
      return LexOpBang(loc, start);
    case '=':
      return LexOpEq(loc, start);
    case '#':
      return LexOpHash(loc, start);
    case '.':
      return LexOpDot(loc, start);
    case ':':
      return LexOpColon(loc, start);
    case '@':
      return LexOpAt(loc, start);
    case '<':
      return LexAngleLeft(loc, start);
    case '>':
      return LexAngleRight(loc, start);
    default:
      break;
  }

  diag_.Error(loc, std::string("unexpected character '") + c + "'");
  Token tok;
  tok.kind = TokenKind::kError;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

// ---------------------------------------------------------------------------
// Bulk lexing
// ---------------------------------------------------------------------------

std::vector<Token> Lexer::LexAll() {
  std::vector<Token> tokens;
  while (true) {
    auto tok = Next();
    tokens.push_back(tok);
    if (tok.IsEof()) {
      break;
    }
  }
  return tokens;
}

}  // namespace delta
