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

  Token NextFilePathSpec();

  std::vector<Token> LexAll();

  // §40.4.1 — an FSM recognition "tool" pragma carried inside a block comment.
  // The current-state form names the vector signal that holds the FSM state and
  // may bind an enumeration name in the same comment; the enum-only form is the
  // separate pragma written immediately after the signal's bit range.
  struct FsmStatePragma {
    enum class Form { kStateVector, kEnumOnly };
    Form form = Form::kStateVector;
    std::string_view signal_name;  // populated for kStateVector
    std::string_view enum_name;    // populated when has_enum is true
    bool has_enum = false;
    SourceLoc loc;
  };

  const std::vector<FsmStatePragma>& FsmStatePragmas() const {
    return fsm_state_pragmas_;
  }

  // §40.4.2 — an FSM "tool" pragma whose current state is held by a part-select
  // of a vector signal. Because the state lives in a part-select rather than a
  // whole signal, the pragma carries an explicit FSM name (which is distinct
  // from the enumeration name) for the coverage tool to report the FSM under.
  struct FsmPartSelectPragma {
    std::string_view signal_name;  // base vector signal of the part-select
    int msb = 0;                   // part-select range [msb:lsb]
    int lsb = 0;
    std::string_view fsm_name;   // required name the FSM is reported under
    std::string_view enum_name;  // enumeration name bound by the `enum` keyword
    SourceLoc loc;
  };

  const std::vector<FsmPartSelectPragma>& FsmPartSelectPragmas() const {
    return fsm_part_select_pragmas_;
  }

  // §40.4.3 — an FSM "tool" pragma whose current state is held by a
  // concatenation of signals. Like the part-select form it carries an explicit
  // FSM name (distinct from the enumeration name) for the coverage tool. The
  // concatenation is composed of every signal listed in the braces; bit-selects
  // and part-selects of those signals are not permitted as members.
  struct FsmConcatPragma {
    std::vector<std::string_view> signal_names;  // members of the concatenation
    std::string_view fsm_name;   // required name the FSM is reported under
    std::string_view enum_name;  // enumeration name bound by the `enum` keyword
    SourceLoc loc;
  };

  const std::vector<FsmConcatPragma>& FsmConcatPragmas() const {
    return fsm_concat_pragmas_;
  }

  struct SavedPos {
    uint32_t pos;
    uint32_t line;
    uint32_t column;
    bool has_peeked;
    bool in_attribute;
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

  void SkipWhitespaceAndComments();
  void ConsumeKeywordMarker();
  uint32_t SkipLineComment();
  uint32_t SkipBlockComment(SourceLoc start_loc);
  void TryRecognizeFsmStatePragma(std::string_view body, SourceLoc loc);
  void TryRecognizeFsmPartSelectPragma(
      const std::vector<std::string_view>& words, SourceLoc loc);
  void TryRecognizeFsmConcatPragma(
      const std::vector<std::string_view>& words, SourceLoc loc);
  static bool IsSimplePragmaIdentifier(std::string_view word);
  static bool ParsePartSelect(std::string_view word, std::string_view& base,
                              int& msb, int& lsb);

  Token MakeToken(TokenKind kind, SourceLoc loc) const;
  Token MakeOp(TokenKind kind, SourceLoc loc, uint32_t start);

  Token LexIdentifier();
  Token LexNumber();
  Token LexStringLiteral();
  bool LexQuotedBody();
  bool LexTripleQuotedBody();
  Token LexSystemIdentifier();
  Token LexEscapedIdentifier();
  Token LexApostrophe();
  Token LexOperator();

  Token LexUnbasedUnsized(SourceLoc loc, uint32_t start);
  Token LexBasedNumber(SourceLoc loc, uint32_t start);
  void ValidateDecimalXZ(SourceLoc loc, char base_letter, uint32_t digit_start);
  void ValidateBaseDigits(SourceLoc loc, char base_letter,
                          uint32_t digit_start);
  void LexFractionalPart();
  void LexExponentPart();
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
  bool has_peeked_ = false;
  bool in_attribute_ = false;
  Token peeked_;
  KeywordVersion keyword_version_ = KeywordVersion::kVer18002023;
  std::vector<FsmStatePragma> fsm_state_pragmas_;
  std::vector<FsmPartSelectPragma> fsm_part_select_pragmas_;
  std::vector<FsmConcatPragma> fsm_concat_pragmas_;
};

}
