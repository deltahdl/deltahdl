#include <cctype>

#include "lexer/lexer.h"

namespace delta {

// Report the first position at or after `p` holding something other than white
// space. §5.3 gives white space as blanks, tabs, newlines and formfeeds, which
// is the set std::isspace answers for. Nothing is consumed, so a caller can ask
// what stands after the white space and still decline to step over it.
uint32_t Lexer::SkipWhitespaceFrom(uint32_t p) const {
  while (p < source_.size() &&
         std::isspace(static_cast<unsigned char>(source_[p]))) {
    ++p;
  }
  return p;
}

// Decide what the apostrophe at the current position opens.
//
// The left brace and left parenthesis are looked for past any white space.
// §5.3 rules that white space "shall be ignored except when they serve to
// separate other lexical tokens", A.8.4 writes the cast as
// `casting_type ' ( expression )` and A.6.7.1 writes `assignment_pattern ::=
// ' { expression { , expression } }`, so the apostrophe and the bracket after
// it are two terminals apiece and `int ' (x)` and `' {1, 2}` are legal.
//
// The single-bit forms are looked for at the next character only. A.8.7 writes
// `unbased_unsigned_literal ::= '0 | '1 | 'x | 'X | 'z | 'Z`, six terminals
// whole, so no white space stands inside one and `' 0` remains the error it is.
// §5.7.1 forbids white space before the base format character in the same way,
// which is why Lexer::ApostropheStartsBaseSpecifier reads past it only to let
// Lexer::LexBasedNumber report the breach.
Token Lexer::LexApostrophe() {
  char next = PeekChar();
  uint32_t after_space = SkipWhitespaceFrom(pos_ + 1);
  char bracket = after_space < source_.size() ? source_[after_space] : '\0';
  if (bracket == '{') {
    auto loc = MakeLoc();
    uint32_t start = pos_;
    while (pos_ <= after_space) {
      Advance();
    }
    return MakeOp(TokenKind::kApostropheLBrace, loc, start);
  }
  if (next == '0' || next == '1' || next == 'x' || next == 'X' || next == 'z' ||
      next == 'Z') {
    return LexNumber();
  }
  if (bracket == '(') {
    auto loc = MakeLoc();
    uint32_t start = pos_;
    Advance();
    return MakeOp(TokenKind::kApostrophe, loc, start);
  }

  if (ApostropheStartsBaseSpecifier(pos_)) {
    return LexBasedNumber(MakeLoc(), pos_);
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

  diag_.Error(loc, std::string("unexpected character '") + c + "'",
              Subclause("5.2"));
  Token tok;
  tok.kind = TokenKind::kError;
  tok.loc = loc;
  tok.text = source_.substr(start, pos_ - start);
  return tok;
}

}  // namespace delta
