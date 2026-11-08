#pragma once

#include <cstddef>
#include <string>
#include <string_view>

inline std::string WithBlockBrokenIntoLines(const std::string& text,
                                            std::string_view opening,
                                            size_t pieces) {
  size_t announced = text.find(opening);
  if (announced == std::string::npos || pieces < 2) return text;
  size_t from = announced + opening.size();
  size_t to = text.find('\n', from);
  if (to == std::string::npos) return text;
  std::string block = text.substr(from, to - from);
  if (block.size() < pieces) return text;
  size_t per = (block.size() + pieces - 1) / pieces;
  std::string broken;
  for (size_t at = 0; at < block.size(); at += per) {
    if (!broken.empty()) broken.push_back('\n');
    broken.append(block, at, per);
  }
  return text.substr(0, from) + broken + text.substr(to);
}
