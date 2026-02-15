#pragma once

#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/keywords.h"
#include "lexer/token.h"

namespace delta {

class Lexer {
 public:
  Lexer(std::string_view source, uint32_t file_id, DiagEngine& diag);

  Token Next();
  Token Peek();

  // Read a file_path_spec token (A.1.1): raw text until whitespace/comma/semi.
  Token NextFilePathSpec();

  std::vector<Token> LexAll();

  // Save/restore lexer position for backtracking (used by parser).
  struct SavedPos {
    uint32_t pos;
    uint32_t line;
    uint32_t column;
    bool has_peeked;
    Token peeked;
    KeywordVersion keyword_version;
  };
  SavedPos SavePos() const;
  void RestorePos(const SavedPos& saved);

 private:
  char Current() const;
  char PeekChar() const;
  void Advance();
  bool AtEnd() const;
  SourceLoc MakeLoc() const;

  // Whitespace / comments
  void SkipWhitespaceAndComments();
  void ConsumeKeywordMarker();
  void SkipLineComment();
  void SkipBlockComment(SourceLoc start_loc);

  // Token construction helpers
  Token MakeToken(TokenKind kind, SourceLoc loc) const;
  Token MakeOp(TokenKind kind, SourceLoc loc, uint32_t start);

  // Primary lexing entry points
  Token LexIdentifier();
  Token LexNumber();
  Token LexStringLiteral();
  void LexQuotedBody();
  bool LexTripleQuotedBody();
  Token LexSystemIdentifier();
  Token LexEscapedIdentifier();
  Token LexApostrophe();
  Token LexOperator();

  // Number sub-helpers
  Token LexUnbasedUnsized(SourceLoc loc, uint32_t start);
  Token LexBasedNumber(SourceLoc loc, uint32_t start);
  void ValidateDecimalXZ(SourceLoc loc, char base_letter, uint32_t digit_start);
  void LexRealSuffix();
  void LexFractionalPart();
  void LexExponentPart();
  bool IsWordBoundary(uint32_t p) const;
  bool TryLexTimeSuffix();

  // Operator sub-helpers
  Token LexOpTilde(SourceLoc loc, uint32_t start);
  Token LexOpPlus(SourceLoc loc, uint32_t start);
  Token LexOpMinus(SourceLoc loc, uint32_t start);
  Token LexOpStar(SourceLoc loc, uint32_t start);
  Token LexOpCaret(SourceLoc loc, uint32_t start);
  Token LexOpAmp(SourceLoc loc, uint32_t start);
  Token LexOpPipe(SourceLoc loc, uint32_t start);
  Token LexOpBang(SourceLoc loc, uint32_t start);
  Token LexOpEq(SourceLoc loc, uint32_t start);
  Token LexOpHash(SourceLoc loc, uint32_t start);
  Token LexOpDot(SourceLoc loc, uint32_t start);
  Token LexOpColon(SourceLoc loc, uint32_t start);
  Token LexOpAt(SourceLoc loc, uint32_t start);
  Token LexOpSlash(SourceLoc loc, uint32_t start);
  Token LexOpPercent(SourceLoc loc, uint32_t start);
  Token LexAngleLeft(SourceLoc loc, uint32_t start);
  Token LexAngleRight(SourceLoc loc, uint32_t start);

  std::string_view source_;
  uint32_t pos_ = 0;
  uint32_t line_ = 1;
  uint32_t column_ = 1;
  uint32_t file_id_;
  DiagEngine& diag_;
  bool has_peeked_ = false;
  bool in_attribute_ = false;
  Token peeked_;
  KeywordVersion keyword_version_ = KeywordVersion::kVer18002023;
};

}  // namespace delta
