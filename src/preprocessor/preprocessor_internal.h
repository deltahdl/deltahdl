#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "lexer/keywords.h"
#include "preprocessor/preprocessor.h"

namespace delta {

struct ActiveLineSplit {
  enum class Kind : std::uint8_t {
    kLeadingDirective,
    kMidLineDirective,
    kPlainText
  } kind;
  size_t split_pos;
};

std::string_view AfterDirective(std::string_view line, std::string_view dir);
std::pair<std::string_view, std::string_view> SplitFirstToken(
    std::string_view s);
std::pair<std::string_view, std::string_view> SplitQuotedArg(
    std::string_view s);
std::pair<std::string_view, std::string_view> SplitTimescaleArg(
    std::string_view s);
ActiveLineSplit ClassifyActiveLine(std::string_view stripped);

struct ActiveLineEmit {
  std::function<void(std::string_view)> expand_and_emit;
  std::function<void(std::string_view)> emit_directive_or_text;
  std::function<void()> report_text_before_include;
};

void EmitActiveLine(std::string_view view, const ActiveLineEmit& emit,
                    std::string& output);

bool StartsWithDirective(std::string_view line, std::string_view dir);

struct LineCursor {
  std::string_view src;
  size_t pos;
  size_t& eol;
  uint32_t& line_num;
};

inline constexpr char kCommentMark = kKeywordMarker;

std::string StripComments(std::string_view line, bool& in_block_comment,
                          bool& in_triple_string,
                          std::vector<std::string>* comments = nullptr);

void RestoreComments(std::string& text, size_t from,
                     const std::vector<std::string>& comments);

bool AtTripleQuote(std::string_view line, size_t i);

size_t EndOfEscapedIdentifier(std::string_view text, size_t i);

enum class StringLiteralState : std::uint8_t {
  kOutside,
  kQuoted,
  kTripleQuoted,
  kEscapedIdentifier
};

inline bool OutsideEveryString(StringLiteralState state) {
  return state == StringLiteralState::kOutside ||
         state == StringLiteralState::kEscapedIdentifier;
}

size_t StepOverStringSyntax(std::string_view line, size_t i,
                            StringLiteralState& state);

bool DefineSpansMultipleLines(std::string_view line);

bool EndsInContinuedQuotedString(std::string_view text);

bool CopyContinuedQuotedString(std::string_view& line, std::string& output,
                               bool& continued);
std::string JoinDefineBody(LineCursor& cursor);
uint32_t JoinMacroUsage(
    LineCursor& cursor,
    const std::function<MacroUsageEnd(std::string_view)>& end_of_macro_usage,
    std::string& joined);

bool StartsWithPragmaDirective(std::string_view line);

}  // namespace delta
