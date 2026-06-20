#include <cctype>

#include "lexer/lexer.h"

namespace delta {

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

}  // namespace delta
