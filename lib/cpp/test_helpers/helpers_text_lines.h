#pragma once

#include <cstddef>
#include <iterator>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

inline bool Holds(std::string_view where, std::string_view what) {
  return where.find(what) != std::string_view::npos;
}

inline size_t TimesWritten(std::string_view where, std::string_view what) {
  size_t written = 0;
  for (size_t at = where.find(what); at != std::string_view::npos;
       at = where.find(what, at + what.size())) {
    ++written;
  }
  return written;
}

inline std::vector<std::string> Tokens(const std::string& content) {
  std::istringstream iss(content);
  return {std::istream_iterator<std::string>(iss),
          std::istream_iterator<std::string>()};
}

inline size_t CountToken(const std::vector<std::string>& toks,
                         std::string_view target) {
  size_t n = 0;
  for (const auto& t : toks) {
    if (t == target) ++n;
  }
  return n;
}

inline std::vector<std::string> Lines(const std::string& out) {
  std::vector<std::string> lines;
  std::istringstream in(out);
  std::string line;
  while (std::getline(in, line)) {
    if (!line.empty()) lines.push_back(line);
  }
  return lines;
}

inline std::vector<std::string> AllLines(const std::string& content) {
  std::vector<std::string> out;
  std::string cur;
  for (char c : content) {
    if (c == '\n') {
      out.push_back(cur);
      cur.clear();
    } else {
      cur.push_back(c);
    }
  }
  if (!cur.empty()) out.push_back(cur);
  return out;
}

inline bool HasLine(const std::vector<std::string>& lines,
                    std::string_view target) {
  for (const auto& l : lines) {
    if (l == target) return true;
  }
  return false;
}

inline size_t CountLine(const std::vector<std::string>& lines,
                        std::string_view target) {
  size_t n = 0;
  for (const auto& l : lines) {
    if (l == target) ++n;
  }
  return n;
}

inline size_t IndexOf(const std::vector<std::string>& toks,
                      std::string_view target) {
  for (size_t i = 0; i < toks.size(); ++i) {
    if (toks[i] == target) return i;
  }
  return toks.size();
}
