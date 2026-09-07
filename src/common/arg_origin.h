#pragma once

#include <string>
#include <vector>

namespace delta {

// Where each word of an options file was written.
//
// `-f` is what puts an option somewhere a reader cannot see: the command line
// names the file, the file names the option, and a report naming only the
// option sends the reader to the command line, where nothing is wrong. An
// options file may name another, so the file a word came from is not the file
// `-f` was given.
//
// `lines` is indexed as argv is, so the word at argv[i] stood on line lines[i]
// of `path`. Index 0 is the program name a caller building an argv fills in,
// which stands on no line of the file.
struct ArgOrigins {
  std::string path;
  std::vector<int> lines;
};

// The "<file>:<line>: " a report about the word at `i` opens with, or nothing
// where the word came from the command line -- which is the case that must go
// on saying what it always said, the command line being in front of the reader
// already. The form is the one the rest of the tool uses for a position.
inline std::string ArgOriginPrefix(const ArgOrigins* origins, int i) {
  if (origins == nullptr || i < 0 ||
      static_cast<size_t>(i) >= origins->lines.size()) {
    return "";
  }
  return origins->path + ":" + std::to_string(origins->lines[i]) + ": ";
}

}  // namespace delta
