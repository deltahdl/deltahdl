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

void Lexer::SkipLineComment() {

  while (!AtEnd() && Current() != '\n') {
    Advance();
  }
}

uint32_t Lexer::SkipBlockComment(SourceLoc start_loc) {

  while (!AtEnd()) {
    if (Current() == '*' && PeekChar() == '/') {
      uint32_t body_end = pos_;
      Advance();
      Advance();
      return body_end;
    }
    Advance();
  }
  diag_.Error(start_loc, "unterminated block comment");
  return pos_;
}

bool Lexer::IsSimplePragmaIdentifier(std::string_view word) {
  if (word.empty()) {
    return false;
  }
  char first = word.front();
  if (!(std::isalpha(static_cast<unsigned char>(first)) || first == '_')) {
    return false;
  }
  for (char c : word) {
    if (!(std::isalnum(static_cast<unsigned char>(c)) || c == '_')) {
      return false;
    }
  }
  return true;
}

void Lexer::TryRecognizeFsmStatePragma(std::string_view body, SourceLoc loc) {
  // Split the comment body into whitespace-delimited words.
  std::vector<std::string_view> words;
  size_t i = 0;
  while (i < body.size()) {
    while (i < body.size() &&
           std::isspace(static_cast<unsigned char>(body[i]))) {
      ++i;
    }
    size_t start = i;
    while (i < body.size() &&
           !std::isspace(static_cast<unsigned char>(body[i]))) {
      ++i;
    }
    if (i > start) {
      words.push_back(body.substr(start, i - start));
    }
  }

  // Every §40.4.1 FSM pragma opens with the required `tool` keyword.
  if (words.empty() || words[0] != "tool") {
    return;
  }

  FsmStatePragma pragma;
  pragma.loc = loc;

  if (words.size() >= 3 && words[1] == "state_vector") {
    // Current-state form: `tool state_vector signal_name`, optionally with a
    // trailing `enum enumeration_name` binding the signal to the FSM.
    if (!IsSimplePragmaIdentifier(words[2])) {
      // A bracketed part-select or braced concatenation is a descendant form
      // (§40.4.2 / §40.4.3), not the simple signal named here.
      return;
    }
    pragma.form = FsmStatePragma::Form::kStateVector;
    pragma.signal_name = words[2];
    if (words.size() == 3) {
      // Bare current-state pragma; the enum name is supplied separately.
    } else if (words.size() == 5 && words[3] == "enum" &&
               IsSimplePragmaIdentifier(words[4])) {
      pragma.has_enum = true;
      pragma.enum_name = words[4];
    } else {
      // An interposed FSM name or other trailing tokens belong to the
      // descendant pragma forms, not the simple §40.4.1 signal pragma.
      return;
    }
  } else if (words.size() == 3 && words[1] == "enum" &&
             IsSimplePragmaIdentifier(words[2])) {
    // Separate `tool enum enumeration_name` pragma placed after the bit range.
    pragma.form = FsmStatePragma::Form::kEnumOnly;
    pragma.has_enum = true;
    pragma.enum_name = words[2];
  } else {
    return;
  }

  // Avoid re-recording the same comment if the lexer backtracks over it.
  for (const auto& existing : fsm_state_pragmas_) {
    if (existing.loc.file_id == loc.file_id && existing.loc.line == loc.line &&
        existing.loc.column == loc.column) {
      return;
    }
  }
  fsm_state_pragmas_.push_back(pragma);
}

void Lexer::SkipWhitespaceAndComments() {
  while (!AtEnd()) {

    if (std::isspace(static_cast<unsigned char>(Current()))) {
      Advance();
      continue;
    }
    if (Current() == kKeywordMarker) {
      ConsumeKeywordMarker();
      continue;
    }

    if (Current() == '/' && PeekChar() == '/') {
      SkipLineComment();
      continue;
    }
    if (Current() == '/' && PeekChar() == '*') {
      auto comment_loc = MakeLoc();
      Advance();
      Advance();
      uint32_t body_start = pos_;
      uint32_t body_end = SkipBlockComment(comment_loc);
      TryRecognizeFsmStatePragma(
          source_.substr(body_start, body_end - body_start), comment_loc);
      continue;
    }
    break;
  }
}

void Lexer::ConsumeKeywordMarker() {
  Advance();
  if (!AtEnd()) {
    keyword_version_ = static_cast<KeywordVersion>(Current());
    Advance();
  }
  if (!AtEnd() && Current() == '\n') {
    Advance();
  }
}

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

    char next = PeekChar();
    if (std::isalnum(static_cast<unsigned char>(next)) || next == '_' ||
        next == '$') {
      return LexSystemIdentifier();
    }
    auto loc = MakeLoc();
    uint32_t start = pos_;
    Advance();
    return MakeOp(TokenKind::kDollar, loc, start);
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
  if (c == '\'') {
    return LexApostrophe();
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

Token Lexer::NextFilePathSpec() {
  has_peeked_ = false;
  SkipWhitespaceAndComments();
  if (AtEnd()) return MakeToken(TokenKind::kEof, MakeLoc());
  auto loc = MakeLoc();
  uint32_t start = pos_;
  while (!AtEnd()) {
    char c = Current();
    if (std::isspace(static_cast<unsigned char>(c)) || c == ',' || c == ';') {
      break;
    }
    Advance();
  }
  if (pos_ == start) {
    diag_.Error(loc, "expected file path specification");
    return MakeToken(TokenKind::kEof, loc);
  }
  Token tok;
  tok.kind = TokenKind::kStringLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

Token Lexer::LexIdentifier() {
  auto loc = MakeLoc();
  uint32_t start = pos_;
  while (!AtEnd() && (std::isalnum(static_cast<unsigned char>(Current())) ||
                      Current() == '_' || Current() == '$')) {
    Advance();
  }
  std::string_view text = source_.substr(start, pos_ - start);
  auto kw = LookupKeyword(text, keyword_version_);
  Token tok;
  tok.kind = kw.value_or(TokenKind::kIdentifier);
  tok.loc = loc;
  tok.text = text;
  if (text.size() > 1024) {
    diag_.Error(loc, "identifier exceeds maximum length of 1024 characters");
  }
  return tok;
}

Token Lexer::LexUnbasedUnsized(SourceLoc loc, uint32_t start) {
  Advance();
  if (!AtEnd()) {
    Advance();
  }
  Token tok;
  tok.kind = TokenKind::kUnbasedUnsizedLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

void Lexer::ValidateDecimalXZ(SourceLoc loc, char base_letter,
                              uint32_t digit_start) {
  if (base_letter != 'd' && base_letter != 'D') return;

  uint32_t digit_count = 0;
  bool has_xz = false;
  for (uint32_t i = digit_start; i < pos_; ++i) {
    char c = source_[i];
    if (c == '_') continue;
    ++digit_count;
    if (c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?') {
      has_xz = true;
    }
  }
  if (has_xz && digit_count > 1) {
    diag_.Error(loc, "x, z, or ? in decimal literal must be the only digit");
  }
}

void Lexer::ValidateBaseDigits(SourceLoc loc, char base_letter,
                               uint32_t digit_start) {
  for (uint32_t i = digit_start; i < pos_; ++i) {
    char c = source_[i];
    if (c == '_' || c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?')
      continue;
    bool valid = false;
    switch (base_letter) {
      case 'b':
      case 'B':
        valid = (c == '0' || c == '1');
        break;
      case 'o':
      case 'O':
        valid = (c >= '0' && c <= '7');
        break;
      case 'd':
      case 'D':
        valid = (c >= '0' && c <= '9');
        break;
      case 'h':
      case 'H':
        valid = std::isxdigit(static_cast<unsigned char>(c));
        break;
    }
    if (!valid) {
      diag_.Error(loc, "illegal digit for specified base");
      return;
    }
  }
}

Token Lexer::LexBasedNumber(SourceLoc loc, uint32_t start) {
  Advance();

  if (!AtEnd() && (Current() == 's' || Current() == 'S')) {
    Advance();
  }
  char base_letter = '\0';
  if (!AtEnd()) {
    base_letter = Current();
    Advance();
  }

  while (!AtEnd() && (Current() == ' ' || Current() == '\t')) {
    Advance();
  }
  uint32_t before_digits = pos_;
  while (!AtEnd() &&
         (std::isxdigit(static_cast<unsigned char>(Current())) ||
          Current() == '_' || Current() == 'x' || Current() == 'z' ||
          Current() == 'X' || Current() == 'Z' || Current() == '?')) {
    Advance();
  }
  if (pos_ == before_digits) {
    diag_.Error(loc, "missing value digits after base specifier");
  }
  if (pos_ > before_digits && source_[before_digits] == '_') {
    diag_.Error(loc, "underscore cannot be first character of number value");
  }
  ValidateBaseDigits(loc, base_letter, before_digits);
  ValidateDecimalXZ(loc, base_letter, before_digits);
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

  uint32_t look = pos_ + 1;
  if (look < source_.size() &&
      (source_[look] == '+' || source_[look] == '-')) {
    ++look;
  }
  if (look >= source_.size() ||
      !std::isdigit(static_cast<unsigned char>(source_[look]))) {
    return;
  }
  Advance();
  if (!AtEnd() && (Current() == '+' || Current() == '-')) {
    Advance();
  }
  while (!AtEnd() && (std::isdigit(static_cast<unsigned char>(Current())) ||
                      Current() == '_')) {
    Advance();
  }
}

bool Lexer::IsWordBoundary(uint32_t p) const {
  return p >= source_.size() ||
         (!std::isalnum(source_[p]) && source_[p] != '_');
}

bool Lexer::TryLexTimeSuffix() {
  if (AtEnd()) return false;
  uint32_t save = pos_;

  if (pos_ + 1 < source_.size()) {
    char c0 = source_[pos_];
    char c1 = source_[pos_ + 1];
    bool is_two_char =
        (c0 == 'm' || c0 == 'u' || c0 == 'n' || c0 == 'p' || c0 == 'f') &&
        c1 == 's';
    if (is_two_char && IsWordBoundary(pos_ + 2)) {
      Advance();
      Advance();
      return true;
    }
  }

  if (source_[pos_] == 's' && IsWordBoundary(pos_ + 1)) {
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

  while (!AtEnd() && (std::isdigit(static_cast<unsigned char>(Current())) ||
                      Current() == '_')) {
    Advance();
  }

  uint32_t before_ws = pos_;
  while (!AtEnd() && (Current() == ' ' || Current() == '\t')) {
    Advance();
  }

  if (!AtEnd() && Current() == '\'') {
    // The size-prefixed integer literal grammar requires the apostrophe to be
    // followed by an optional s/S signed marker and one of the base letters
    // d/D/b/B/o/O/h/H. Anything else — most importantly a left parenthesis or
    // left brace — keeps the apostrophe as a separate token so that
    // size'(expr) and size'{...} cast/assignment-pattern forms tokenize
    // correctly.
    uint32_t look = pos_ + 1;
    if (look < source_.size() &&
        (source_[look] == 's' || source_[look] == 'S')) {
      ++look;
    }
    char base = (look < source_.size()) ? source_[look] : '\0';
    bool looks_like_base = base == 'd' || base == 'D' || base == 'b' ||
                           base == 'B' || base == 'o' || base == 'O' ||
                           base == 'h' || base == 'H';
    if (looks_like_base) {
      return LexBasedNumber(loc, start);
    }
  }
  pos_ = before_ws;

  uint32_t before_real = pos_;
  LexFractionalPart();
  uint32_t before_exp = pos_;
  LexExponentPart();
  bool has_exponent = (pos_ != before_exp);
  bool is_real = (pos_ != before_real);

  bool is_time = !has_exponent && TryLexTimeSuffix();

  Token tok;
  tok.kind = is_time   ? TokenKind::kTimeLiteral
             : is_real ? TokenKind::kRealLiteral
                       : TokenKind::kIntLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

Token Lexer::LexStringLiteral() {
  auto loc = MakeLoc();
  uint32_t start = pos_;

  bool triple = PeekChar() == '"' && pos_ + 2 < source_.size() &&
                source_[pos_ + 2] == '"';
  if (triple) {
    Advance();
    Advance();
    Advance();
    if (!LexTripleQuotedBody()) {
      diag_.Error(loc, "unterminated triple-quoted string");
    }
  } else {
    Advance();
    if (!LexQuotedBody()) {
      diag_.Error(loc, "unterminated string literal");
    }
  }
  Token tok;
  tok.kind = TokenKind::kStringLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

bool Lexer::LexQuotedBody() {
  while (!AtEnd() && Current() != '"') {
    if (Current() == '\n' || Current() == '\r') {

      return false;
    }
    if (Current() == '\\') {
      Advance();

      if (AtEnd()) return false;
    }
    Advance();
  }
  if (AtEnd()) return false;
  Advance();
  return true;
}

bool Lexer::LexTripleQuotedBody() {
  while (!AtEnd()) {
    if (Current() == '"' && PeekChar() == '"' && pos_ + 2 < source_.size() &&
        source_[pos_ + 2] == '"') {
      Advance();
      Advance();
      Advance();
      return true;
    }
    if (Current() == '\\') {
      Advance();
    }
    Advance();
  }
  return false;
}

Token Lexer::LexSystemIdentifier() {
  auto loc = MakeLoc();
  uint32_t start = pos_;
  Advance();
  while (!AtEnd()) {
    char ch = Current();
    bool is_word =
        std::isalnum(static_cast<unsigned char>(ch)) || ch == '_' || ch == '$';
    if (!is_word) break;
    Advance();
  }
  Token tok;
  tok.kind = TokenKind::kSystemIdentifier;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  if (tok.text.size() > 1024) {
    diag_.Error(loc, "identifier exceeds maximum length of 1024 characters");
  }
  return tok;
}

Token Lexer::LexEscapedIdentifier() {
  auto loc = MakeLoc();
  Advance();
  uint32_t start = pos_;
  while (!AtEnd()) {
    unsigned char c = static_cast<unsigned char>(Current());
    if (std::isspace(c)) {
      break;
    }

    if (c < 33 || c > 126) {
      diag_.Error(MakeLoc(),
                  "escaped identifier contains non-printable character");
    }
    Advance();
  }
  Token tok;
  tok.kind = TokenKind::kEscapedIdentifier;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  if (tok.text.size() > 1024) {
    diag_.Error(loc, "identifier exceeds maximum length of 1024 characters");
  }
  return tok;
}

static bool IsBaseSpecifier(char c) {
  return c == 'h' || c == 'H' || c == 'd' || c == 'D' || c == 'b' || c == 'B' ||
         c == 'o' || c == 'O';
}

Token Lexer::LexApostrophe() {
  char next = PeekChar();
  if (next == '{') {
    auto loc = MakeLoc();
    uint32_t start = pos_;
    Advance();
    Advance();
    return MakeOp(TokenKind::kApostropheLBrace, loc, start);
  }
  if (next == '0' || next == '1' || next == 'x' || next == 'X' || next == 'z' ||
      next == 'Z') {
    return LexNumber();
  }
  if (next == '(') {
    auto loc = MakeLoc();
    uint32_t start = pos_;
    Advance();
    return MakeOp(TokenKind::kApostrophe, loc, start);
  }

  if (IsBaseSpecifier(next)) {
    return LexBasedNumber(MakeLoc(), pos_);
  }
  if (next == 's' || next == 'S') {

    if (pos_ + 2 < source_.size() && IsBaseSpecifier(source_[pos_ + 2])) {
      return LexBasedNumber(MakeLoc(), pos_);
    }
  }
  return LexOperator();
}

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
  if (!AtEnd() && Current() == ':') {
    Advance();
    return MakeOp(TokenKind::kPlusColon, loc, start);
  }

  if (!AtEnd() && Current() == '/' && pos_ + 1 < source_.size() &&
      source_[pos_ + 1] == '-') {
    Advance();
    Advance();
    return MakeOp(TokenKind::kPlusSlashMinus, loc, start);
  }
  if (!AtEnd() && Current() == '%' && pos_ + 1 < source_.size() &&
      source_[pos_ + 1] == '-') {
    Advance();
    Advance();
    return MakeOp(TokenKind::kPlusPercentMinus, loc, start);
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
  if (!AtEnd() && Current() == ':') {
    Advance();
    return MakeOp(TokenKind::kMinusColon, loc, start);
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
  if (!AtEnd() && Current() == '-' && pos_ + 1 < source_.size() &&
      source_[pos_ + 1] == '#') {
    Advance();
    Advance();
    return MakeOp(TokenKind::kHashMinusHash, loc, start);
  }
  if (!AtEnd() && Current() == '=' && pos_ + 1 < source_.size() &&
      source_[pos_ + 1] == '#') {
    Advance();
    Advance();
    return MakeOp(TokenKind::kHashEqHash, loc, start);
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
  if (Current() == '-' && pos_ + 1 < source_.size() &&
      source_[pos_ + 1] == '>') {
    Advance();
    Advance();
    return MakeOp(TokenKind::kLtDashGt, loc, start);
  }
  if (Current() != '<') {
    return MakeOp(TokenKind::kLt, loc, start);
  }
  Advance();
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
  Advance();
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

Token Lexer::LexOperator() {
  auto loc = MakeLoc();
  uint32_t start = pos_;
  char c = Current();
  Advance();

  switch (c) {
    case '(':
      if (!AtEnd() && Current() == '*' && PeekChar() != ')') {
        Advance();
        in_attribute_ = true;
        return MakeOp(TokenKind::kAttrStart, loc, start);
      }
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
      if (in_attribute_ && !AtEnd() && Current() == ')') {
        Advance();
        in_attribute_ = false;
        return MakeOp(TokenKind::kAttrEnd, loc, start);
      }
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

Lexer::SavedPos Lexer::SavePos() const {
  return {pos_,          line_,   column_,         has_peeked_,
          in_attribute_, peeked_, keyword_version_};
}

void Lexer::RestorePos(const SavedPos& saved) {
  pos_ = saved.pos;
  line_ = saved.line;
  column_ = saved.column;
  has_peeked_ = saved.has_peeked;
  in_attribute_ = saved.in_attribute;
  peeked_ = saved.peeked;
  keyword_version_ = saved.keyword_version;
}

}
