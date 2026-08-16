// The number-lexing members of Lexer. §5.7 and §5.8 give the literals read
// here: based and unbased-unsized integers, real numbers with a fractional or
// exponent part, and the time literals of §5.8. Lexer::Next dispatches into
// Lexer::LexNumber, and Lexer::LexApostrophe in src/lexer/lexer_operators.cpp
// calls Lexer::ApostropheStartsBaseSpecifier; every other call among these
// members comes from one of the others. The declarations are in
// src/lexer/lexer.h, so a caller needs no include beyond the ones it already
// has.

#include <cctype>

#include "lexer/lexer.h"

namespace delta {

// Decide whether the apostrophe at `apostrophe_pos` opens a based integer
// literal. §5.7.1 makes the size constant optional, so both callers ask this:
// Lexer::LexNumber of the apostrophe that follows a size, as in 8'h99, and
// Lexer::LexApostrophe of an apostrophe written without one, as in 'h99. The
// grammar requires an optional s/S signed marker and then one of the base
// letters d/D/b/B/o/O/h/H. Anything else — most importantly a left
// parenthesis or left brace — keeps the apostrophe a separate token so that
// the '(expr) and '{...} cast and assignment-pattern forms tokenize
// correctly.
//
// Spaces and tabs standing before the signed marker or before the base letter
// are read past, so that `8' h99` and `' h99` reach Lexer::LexBasedNumber and
// are reported there against the §5.7.1 sentence forbidding white space
// between the apostrophe and the base format character. What follows the white
// space still has to be a base letter, so the answer stays false for `'(x)`
// and `4' (x)`, for `'{...}` and `4' {...}`, and for the unsized single-bit
// forms '0, '1, 'x and 'z.
bool Lexer::ApostropheStartsBaseSpecifier(uint32_t apostrophe_pos) const {
  auto skip_spaces_and_tabs = [this](uint32_t p) {
    while (p < source_.size() && (source_[p] == ' ' || source_[p] == '\t')) {
      ++p;
    }
    return p;
  };
  uint32_t look = skip_spaces_and_tabs(apostrophe_pos + 1);
  if (look < source_.size() && (source_[look] == 's' || source_[look] == 'S')) {
    look = skip_spaces_and_tabs(look + 1);
  }
  char base = (look < source_.size()) ? source_[look] : '\0';
  return base == 'd' || base == 'D' || base == 'b' || base == 'B' ||
         base == 'o' || base == 'O' || base == 'h' || base == 'H';
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
    diag_.Error(loc, "x, z, or ? in decimal literal must be the only digit",
                Subclause("5.7.1"));
  }
}

// Reports which sentence of §5.7.1 a based literal broke when its value run
// collected nothing, given a lexer positioned at the character that stopped the
// run. `loc` is the start of the literal, which is where both reports stand.
void Lexer::ReportMissingValueToken(SourceLoc loc) {
  if (!AtEnd() && (Current() == '+' || Current() == '-')) {
    // §5.7.1: "A plus or minus operator between the base format and the number
    // is an illegal syntax", which Example 3 writes as `8 'd -6`. The sign is
    // no part of the value token, so a literal written with one arrives here
    // with an empty run and the sign still unread.
    diag_.Error(loc,
                "plus or minus operator between the base format and the number "
                "is illegal syntax",
                Subclause("5.7.1"));
    return;
  }
  diag_.Error(loc, "missing value digits after base specifier",
              Subclause("5.7.1"));
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
      default:
        break;
    }
    if (!valid) {
      diag_.Error(loc, "illegal digit for specified base", Subclause("5.7.1"));
      return;
    }
  }
}

Token Lexer::LexBasedNumber(SourceLoc loc, uint32_t start) {
  Advance();

  // §5.7.1: "The apostrophe character and the base format character shall not
  // be separated by any white space." The optional s/S signed marker stands
  // between them, so white space is forbidden on either side of it. Read the
  // literal as it was written whatever the answer, so that one token still
  // spans it, and report the sentence once even when both places carry white
  // space.
  bool space_before_sign = SkipSpacesAndTabs();
  if (!AtEnd() && (Current() == 's' || Current() == 'S')) {
    Advance();
  }
  bool space_before_base = SkipSpacesAndTabs();
  if (space_before_sign || space_before_base) {
    diag_.Error(loc,
                "white space shall not separate the apostrophe from the base "
                "format character",
                Subclause("5.7.1"));
  }
  char base_letter = '\0';
  if (!AtEnd()) {
    base_letter = Current();
    Advance();
  }

  // §5.7.1: "The unsigned number token shall immediately follow the base
  // format, optionally preceded by white space." This white space is legal, so
  // stepping over it draws no report.
  SkipSpacesAndTabs();
  uint32_t before_digits = pos_;
  // §5.7.1: "The third token, an unsigned number, shall consist of digits that
  // are legal for the specified base format." A letter or digit that is illegal
  // for the base is still written where the value token belongs, so the run
  // covers every alphanumeric character and Lexer::ValidateBaseDigits judges
  // what it collected against the base. Ending the run at the first character
  // no base accepts would hand that function a span it can never reject for a
  // hexadecimal literal, and would leave `4'hG` reported as a literal carrying
  // no value at all.
  while (!AtEnd() && (std::isalnum(static_cast<unsigned char>(Current())) ||
                      Current() == '_' || Current() == '?')) {
    Advance();
  }
  if (pos_ == before_digits) {
    ReportMissingValueToken(loc);
  }
  if (pos_ > before_digits && source_[before_digits] == '_') {
    diag_.Error(loc, "underscore cannot be first character of number value",
                Subclause("5.7.1"));
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
  if (look < source_.size() && (source_[look] == '+' || source_[look] == '-')) {
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

  // §5.7.1 permits white space between the size and the apostrophe, as
  // Example 2's `5 'D 3` writes it, so reading past white space is the only way
  // to learn whether this number ends here or carries a base specifier. Both
  // counters are put back when it does not: Advance() moved column_ over the
  // white space, SkipWhitespaceAndComments() moves it over the same characters
  // again before the next token, and a column counted twice locates that token
  // and every later one on the line past where it is written.
  uint32_t before_ws = pos_;
  uint32_t column_before_ws = column_;
  SkipSpacesAndTabs();

  if (!AtEnd() && Current() == '\'' && ApostropheStartsBaseSpecifier(pos_)) {
    return LexBasedNumber(loc, start);
  }
  pos_ = before_ws;
  column_ = column_before_ws;

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

}  // namespace delta
