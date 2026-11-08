#pragma once

#include <cstddef>
#include <cstdint>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "cstddef"
#include "lexer/keywords.h"
#include "lexer/token.h"

namespace delta {

enum class TextOrigin : std::uint8_t { kUserSource, kPreprocessorOutput };

class Lexer {
 public:
  Lexer(std::string_view source, uint32_t file_id, DiagEngine& diag,
        TextOrigin origin = TextOrigin::kUserSource);

  Token Next();
  Token Peek();
  SourceLoc TakenEnd() const;

  Token NextFilePathSpec();

  std::vector<Token> LexAll();

  const std::unordered_set<std::string_view>& DottedEscapedNames() const {
    return dotted_escaped_names_;
  }

  struct FsmStatePragma {
    enum class Form : std::uint8_t { kStateVector, kEnumOnly };
    Form form = Form::kStateVector;
    std::string_view signal_name;
    std::string_view enum_name;
    bool has_enum = false;
    SourceLoc loc;
  };

  const std::vector<FsmStatePragma>& FsmStatePragmas() const {
    return fsm_state_pragmas_;
  }

  struct FsmPartSelectPragma {
    std::string_view signal_name;
    int msb = 0;
    int lsb = 0;
    std::string_view fsm_name;
    std::string_view enum_name;
    SourceLoc loc;
  };

  const std::vector<FsmPartSelectPragma>& FsmPartSelectPragmas() const {
    return fsm_part_select_pragmas_;
  }

  struct FsmConcatPragma {
    std::vector<std::string_view> signal_names;
    std::string_view fsm_name;
    std::string_view enum_name;
    SourceLoc loc;
  };

  const std::vector<FsmConcatPragma>& FsmConcatPragmas() const {
    return fsm_concat_pragmas_;
  }

  std::string_view ClaimFsmEnumPragma(SourceLoc before);

  struct SavedPos {
    uint32_t pos;
    uint32_t line;
    uint32_t column;
    bool has_peeked;
    bool in_attribute;
    Token peeked;
    KeywordVersion keyword_version;
    std::size_t fsm_pragmas_claimed;
  };
  SavedPos SavePos() const;
  void RestorePos(const SavedPos& saved);

 private:
  Token Scan();
  char CharAt(uint32_t p) const;
  char Current() const;
  char PeekChar() const;
  void Advance();
  bool AtEnd() const;
  SourceLoc MakeLoc() const;

  static bool IsWhiteSpace(char c);
  void SkipWhitespaceAndComments();
  bool SkipSpacesAndTabs();
  uint32_t SkipWhitespaceFrom(uint32_t p) const;
  void ConsumeKeywordMarker();
  uint32_t SkipLineComment();
  uint32_t SkipBlockComment(SourceLoc start_loc);
  void TryRecognizeFsmStatePragma(std::string_view body, SourceLoc loc);
  void TryRecognizeFsmPartSelectPragma(
      const std::vector<std::string_view>& words, SourceLoc loc);
  void TryRecognizeFsmConcatPragma(const std::vector<std::string_view>& words,
                                   SourceLoc loc);
  void ReportConcatSelectProhibition(std::string_view inside, SourceLoc loc);

 public:
  static bool IsSimplePragmaIdentifier(std::string_view word);

 private:
  static bool ParsePartSelect(std::string_view word, std::string_view& base,
                              int& msb, int& lsb);

  Token MakeToken(TokenKind kind, SourceLoc loc) const;
  Token MakeOp(TokenKind kind, SourceLoc loc, uint32_t start);

  Token LexIdentifier();
  Token LexNumber();
  Token LexStringLiteral();
  bool LexQuotedBody();
  bool LexTripleQuotedBody();
  void CheckEscapeDigits();
  Token LexSystemIdentifier();
  Token LexEscapedIdentifier();
  Token LexApostrophe();
  Token LexOperator();

  Token LexUnbasedUnsized(SourceLoc loc, uint32_t start);
  Token LexBasedNumber(SourceLoc loc, uint32_t start);
  bool ApostropheStartsBaseSpecifier(uint32_t apostrophe_pos) const;
  void ReportMissingValueToken(SourceLoc loc);
  void ValidateDecimalXZ(SourceLoc loc, char base_letter, uint32_t digit_start);
  void ValidateBaseDigits(SourceLoc loc, char base_letter,
                          uint32_t digit_start);
  void LexFractionalPart();
  void LexExponentPart();
  Token LexRealMissingDigit(SourceLoc loc, uint32_t start, const char* side);
  bool IsWordBoundary(uint32_t p) const;
  bool TryLexTimeSuffix();

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
  TextOrigin origin_;
  bool has_peeked_ = false;
  bool in_attribute_ = false;
  Token peeked_;
  Token taken_;
  KeywordVersion keyword_version_ = KeywordVersion::kVer18002023;
  std::vector<FsmStatePragma> fsm_state_pragmas_;
  std::vector<FsmPartSelectPragma> fsm_part_select_pragmas_;
  std::vector<FsmConcatPragma> fsm_concat_pragmas_;
  std::unordered_set<std::string_view> dotted_escaped_names_;
  uint32_t first_unseen_comment_ = 0;
  std::size_t fsm_pragmas_claimed_ = 0;
};

}  // namespace delta
