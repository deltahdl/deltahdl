#pragma once

#include <cstddef>
#include <string_view>

#include "parser/ast.h"

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

}  // namespace delta
