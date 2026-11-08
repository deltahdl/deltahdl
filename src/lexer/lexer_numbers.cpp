#include <cctype>
#include <cstdint>
#include <string>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/lexer.h"
#include "lexer/token.h"

namespace delta {

bool Lexer::ApostropheStartsBaseSpecifier(uint32_t apostrophe_pos) const {
  auto skip_spaces_and_tabs = [this](uint32_t p) {
    while (CharAt(p) == ' ' || CharAt(p) == '\t') {
      ++p;
    }
    return p;
  };
  uint32_t look = skip_spaces_and_tabs(apostrophe_pos + 1);
  if (CharAt(look) == 's' || CharAt(look) == 'S') {
    look = skip_spaces_and_tabs(look + 1);
  }
  char base = CharAt(look);
  return base == 'd' || base == 'D' || base == 'b' || base == 'B' ||
         base == 'o' || base == 'O' || base == 'h' || base == 'H';
}

Token Lexer::LexUnbasedUnsized(SourceLoc loc, uint32_t start) {
  Advance();
  Advance();
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

void Lexer::ReportMissingValueToken(SourceLoc loc) {
  if ((Current() == '+' || Current() == '-')) {
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
        valid = c <= '7';
        break;
      case 'd':
      case 'D':
        valid = c <= '9';
        break;
      default:
        valid = std::isxdigit(static_cast<unsigned char>(c));
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

  bool space_before_sign = SkipSpacesAndTabs();
  if ((Current() == 's' || Current() == 'S')) {
    Advance();
  }
  bool space_before_base = SkipSpacesAndTabs();
  if (space_before_sign || space_before_base) {
    diag_.Error(loc,
                "the apostrophe, any 's', and the base format character of a "
                "based number must be written together without white space",
                Subclause("5.7.1"));
  }
  char base_letter = Current();
  Advance();

  while (IsWhiteSpace(Current())) Advance();
  uint32_t before_digits = pos_;
  while ((std::isalnum(static_cast<unsigned char>(Current())) ||
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
  if (Current() != '.') return;
  Advance();
  while ((std::isdigit(static_cast<unsigned char>(Current())) ||
          Current() == '_')) {
    Advance();
  }
}

void Lexer::LexExponentPart() {
  if (Current() != 'e' && Current() != 'E') return;

  uint32_t look = pos_ + 1;
  if (CharAt(look) == '+' || CharAt(look) == '-') {
    ++look;
  }
  if (!std::isdigit(static_cast<unsigned char>(CharAt(look)))) {
    return;
  }
  Advance();
  if ((Current() == '+' || Current() == '-')) {
    Advance();
  }
  while ((std::isdigit(static_cast<unsigned char>(Current())) ||
          Current() == '_')) {
    Advance();
  }
}

Token Lexer::LexRealMissingDigit(SourceLoc loc, uint32_t start,
                                 const char* side) {
  while ((std::isdigit(static_cast<unsigned char>(Current())) ||
          Current() == '_')) {
    Advance();
  }
  LexExponentPart();
  Token tok;
  tok.kind = TokenKind::kRealLiteral;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  diag_.Error(loc,
              "real literal '" + std::string(tok.text) + "' has no digit " +
                  side + " its decimal point",
              Subclause("5.7.2"));
  return tok;
}

bool Lexer::IsWordBoundary(uint32_t p) const {
  char c = CharAt(p);
  return !std::isalnum(static_cast<unsigned char>(c)) && c != '_';
}

bool Lexer::TryLexTimeSuffix() {
  char c0 = Current();
  bool is_two_char =
      (c0 == 'm' || c0 == 'u' || c0 == 'n' || c0 == 'p' || c0 == 'f') &&
      PeekChar() == 's';
  if (is_two_char && IsWordBoundary(pos_ + 2)) {
    Advance();
    Advance();
    return true;
  }
  if (c0 == 's' && IsWordBoundary(pos_ + 1)) {
    Advance();
    return true;
  }
  return false;
}

Token Lexer::LexNumber() {
  auto loc = MakeLoc();
  uint32_t start = pos_;

  if (Current() == '\'') {
    return LexUnbasedUnsized(loc, start);
  }

  while ((std::isdigit(static_cast<unsigned char>(Current())) ||
          Current() == '_')) {
    Advance();
  }

  uint32_t before_ws = pos_;
  uint32_t column_before_ws = column_;
  SkipSpacesAndTabs();

  if (Current() == '\'' && ApostropheStartsBaseSpecifier(pos_)) {
    return LexBasedNumber(loc, start);
  }
  pos_ = before_ws;
  column_ = column_before_ws;

  if (Current() == '.' &&
      !std::isdigit(static_cast<unsigned char>(PeekChar()))) {
    Advance();
    return LexRealMissingDigit(loc, start, "after");
  }

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
