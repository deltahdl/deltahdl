#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <utility>

#include "preprocessor/preprocessor.h"

namespace delta {

// How a comment-stripped active line (22.2) should be split: either it opens
// with a directive, contains a directive after a language element, or is wholly
// ordinary text. The directive part begins at split_pos; any leading text spans
// [0, split_pos).
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

bool StartsWithDirective(std::string_view line, std::string_view dir);

// Per-line scan position over the source buffer driven by the preprocessing
// loop (22.x): `src` is the whole file text, `pos` the start offset of the
// current physical line, `eol` its end offset (advanced when a `define body is
// joined across continuation lines, or a macro usage across the lines its
// argument list runs onto), and `line_num` the 1-based line counter.
struct LineCursor {
  std::string_view src;
  size_t pos;
  size_t& eol;
  uint32_t& line_num;
};

// Blanks the body of every A.9.2 comment on `line`, keeping the delimiters,
// and leaves what a string literal holds alone; the two flags carry a block
// comment and a triple_quoted_string from one line to the next. Defined in
// src/preprocessor/preprocessor.cpp beside the loop that strips each line it
// emits, and read by src/preprocessor/preprocessor_join.cpp, which strips the
// lines it reads ahead the same way.
std::string StripComments(std::string_view line, bool& in_block_comment,
                          bool& in_triple_string);

// The two ways a construct runs onto the physical lines after the one it opens
// on, both in src/preprocessor/preprocessor_join.cpp: a `define body continued
// by a backslash, an open block comment or an open triple_quoted_string
// (22.5.1), and a function-like macro usage whose actual argument list is
// still open at the end of its line (22.5.1). Each moves the cursor to the
// last line it read.
bool DefineSpansMultipleLines(std::string_view line);
std::string JoinDefineBody(LineCursor& cursor);
// Returns the number of lines read beyond the first, or 0 when nothing was
// joined; `end_of_macro_usage` is Preprocessor::EndOfMacroUsage, reached
// through a callback because the macro table it reads is private.
uint32_t JoinMacroUsage(
    LineCursor& cursor,
    const std::function<MacroUsageEnd(std::string_view)>& end_of_macro_usage,
    std::string& joined);

// Whether `line` opens a `pragma directive. None of §34.5.9.2's coding schemes
// spells one, so this is what a line of a protected block can never be, and it
// is how the reader of a block spanning several lines knows the block ended.
bool StartsWithPragmaDirective(std::string_view line);

}  // namespace delta
