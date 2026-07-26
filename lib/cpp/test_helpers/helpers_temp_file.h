#pragma once

#include <fstream>
#include <ios>
#include <iterator>
#include <string>

// Whole-file reads and writes for a test whose subject is a file on disk --
// the data a file-reading system task consumes, or the file a file-writing one
// leaves behind. Both work in bytes and neither interprets the contents, so a
// test that cares about exact spacing or line endings sees them unchanged.

// Creates `path` holding exactly `content`, replacing whatever was there. The
// stream is binary, so `content` reaches the file byte for byte.
inline void SeedFile(const std::string& path, const std::string& content) {
  std::ofstream ofs(path, std::ios::binary);
  ofs << content;
}

// The entire contents of `path`, or the empty string when it cannot be opened.
inline std::string SlurpFile(const std::string& path) {
  std::ifstream ifs(path);
  return std::string((std::istreambuf_iterator<char>(ifs)),
                     std::istreambuf_iterator<char>());
}
