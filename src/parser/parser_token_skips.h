#pragma once

#include "lexer/lexer.h"
#include "lexer/token.h"

namespace delta {

// The token tests and skips the parser's translation units share, kept out of
// parser.h because they are free functions over the lexer rather than parts of
// the Parser.

inline bool IsPortDirection(TokenKind tk) {
  return tk == TokenKind::kKwInput || tk == TokenKind::kKwOutput ||
         tk == TokenKind::kKwInout || tk == TokenKind::kKwRef;
}

// Reads past the ';' that ends the construct at the current position, or to
// the end of input where there is none, for a construct reported whole.
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

// The keywords that open a data_type of A.2.2.1 by themselves, which is what
// parser_stmt.cpp's for-initialization and parser_block_item_decl.cpp's block
// item predicate both ask of a token before reading a declaration.
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
    // A.2.2.1 gives data_type the bare alternative `event`, so an event
    // declaration is a data_declaration and A.2.8's block_item_declaration
    // carries it wherever A.6.3's seq_block and par_block and A.2.6's and
    // A.2.7's subroutine bodies put one. Without it the line was read as an
    // expression statement, the event was never declared, and every later
    // reference to the name resolved to whatever else it happened to mean --
    // which is how §15.5's synchronization between two arms of a fork is
    // written.
    case TokenKind::kKwEvent:
      return true;
    default:
      return false;
  }
}

// The assignment_operator alternatives of A.6.2 other than `=`, which
// parser_stmt.cpp reads as an operator and parser_block_item_decl.cpp reads as
// the sign that a leading name is a statement.
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

}  // namespace delta
