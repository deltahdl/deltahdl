#pragma once

#include <cstddef>
#include <string>
#include <string_view>

#include "preprocessor/protect_encoding.h"

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

struct ProtectBlockLine {
  size_t from = std::string_view::npos;
  size_t size = 0;
};

inline ProtectBlockLine ProtectBlockLineAfter(std::string_view text,
                                              std::string_view opening) {
  ProtectBlockLine line;
  size_t opened = text.find(opening);
  if (opened == std::string_view::npos) return line;
  line.from = opened + opening.size();
  size_t ends = text.find('\n', line.from);
  line.size = (ends == std::string_view::npos ? text.size() : ends) - line.from;
  return line;
}

inline bool ProtectBlockBytesAfter(std::string_view text,
                                   std::string_view opening,
                                   std::string_view enctype,
                                   std::string* bytes) {
  ProtectBlockLine line = ProtectBlockLineAfter(text, opening);
  if (line.from == std::string_view::npos) return false;
  return delta::DecodeProtectBlock(text.substr(line.from, line.size), enctype,
                                   bytes);
}

inline std::string WithProtectBlockBytes(std::string text,
                                         std::string_view opening,
                                         std::string_view bytes,
                                         std::string_view enctype) {
  ProtectBlockLine line = ProtectBlockLineAfter(text, opening);
  if (line.from == std::string_view::npos) return text;
  delta::ProtectEncoding encoding;
  encoding.enctype = std::string(enctype);
  text.replace(line.from, line.size,
               delta::EncodeProtectBlock(bytes, encoding));
  return text;
}
