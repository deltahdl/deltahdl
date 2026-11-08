#pragma once

#include <string_view>

#include "lexer/lexer.h"
#include "lexer/token.h"

namespace delta {

inline bool IsPortDirection(TokenKind tk) {
  return tk == TokenKind::kKwInput || tk == TokenKind::kKwOutput ||
         tk == TokenKind::kKwInout || tk == TokenKind::kKwRef;
}

inline bool IsElabSeverityTask(TokenKind kind, std::string_view text) {
  return kind == TokenKind::kSystemIdentifier &&
         (text == "$fatal" || text == "$error" || text == "$warning" ||
          text == "$info");
}

inline bool IsTimeunitKeyword(TokenKind kind) {
  return kind == TokenKind::kKwTimeunit || kind == TokenKind::kKwTimeprecision;
}

inline void SkipToSemicolon(Lexer& lexer) {
  while (!lexer.Peek().Is(TokenKind::kSemicolon) &&
         !lexer.Peek().Is(TokenKind::kEof)) {
    lexer.Next();
  }
  if (lexer.Peek().Is(TokenKind::kSemicolon)) lexer.Next();
}

inline void SkipBraceBlock(Lexer& lexer) {
  int depth = 1;
  while (depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (lexer.Peek().Is(TokenKind::kLBrace)) ++depth;
    if (lexer.Peek().Is(TokenKind::kRBrace)) --depth;
    if (depth > 0) lexer.Next();
  }
  if (lexer.Peek().Is(TokenKind::kRBrace)) lexer.Next();
}

inline bool IsDataTypeKeyword(TokenKind tk) {
  switch (tk) {
    case TokenKind::kKwLogic:
    case TokenKind::kKwReg:
    case TokenKind::kKwBit:
    case TokenKind::kKwByte:
    case TokenKind::kKwShortint:
    case TokenKind::kKwInt:
    case TokenKind::kKwLongint:
    case TokenKind::kKwInteger:
    case TokenKind::kKwReal:
    case TokenKind::kKwShortreal:
    case TokenKind::kKwRealtime:
    case TokenKind::kKwTime:
    case TokenKind::kKwString:
    case TokenKind::kKwChandle:
    case TokenKind::kKwEvent:
      return true;
    default:
      return false;
  }
}

inline bool IsCompoundAssignOp(TokenKind kind) {
  switch (kind) {
    case TokenKind::kPlusEq:
    case TokenKind::kMinusEq:
    case TokenKind::kStarEq:
    case TokenKind::kSlashEq:
    case TokenKind::kPercentEq:
    case TokenKind::kAmpEq:
    case TokenKind::kPipeEq:
    case TokenKind::kCaretEq:
    case TokenKind::kLtLtEq:
    case TokenKind::kGtGtEq:
    case TokenKind::kLtLtLtEq:
    case TokenKind::kGtGtGtEq:
      return true;
    default:
      return false;
  }
}

inline bool TokenFollowsDirectly(const Token& first, const Token& next) {
  return next.text.data() == first.text.data() + first.text.size();
}

}  // namespace delta
