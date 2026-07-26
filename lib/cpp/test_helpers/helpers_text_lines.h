#pragma once

#include <cstddef>
#include <iterator>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

// Splitting and searching the text a test captured -- a dump file, a tool's
// stdout, a lexer's token spellings. Shared so that "the output has this line"
// means the same thing in every test that asks it.

// The text split into its white-space-delimited tokens. For a free-format
// language this projection alone -- no line or column information -- is enough
// to recover every construct the text spells.
inline std::vector<std::string> Tokens(const std::string& content) {
  std::istringstream iss(content);
  return {std::istream_iterator<std::string>(iss),
          std::istream_iterator<std::string>()};
}

// Occurrences of `target` as a complete token, never as a substring.
inline size_t CountToken(const std::vector<std::string>& toks,
                         std::string_view target) {
  size_t n = 0;
  for (const auto& t : toks) {
    if (t == target) ++n;
  }
  return n;
}

// Splits captured stdout into its non-empty lines.
inline std::vector<std::string> Lines(const std::string& out) {
  std::vector<std::string> lines;
  std::istringstream in(out);
  std::string line;
  while (std::getline(in, line)) {
    if (!line.empty()) lines.push_back(line);
  }
  return lines;
}

// Whether any line matches `target` exactly.
inline bool HasLine(const std::vector<std::string>& lines,
                    std::string_view target) {
  for (const auto& l : lines) {
    if (l == target) return true;
  }
  return false;
}
