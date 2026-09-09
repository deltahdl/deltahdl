#pragma once

#include <cstddef>
#include <string>
#include <string_view>

// Presenting a §34.5 protected block on more lines than the tool wrote it on.
//
// §34.5.15.2 has a data block "begin on the next line in the file" and says
// nothing about where it ends, and §34.5.22.2 and §34.5.27.2 word the digest
// block and the key block the same way. So one block written on one line and
// the same block written on three are the same block: §34.5.9's count is of the
// bytes the characters stand for rather than of the characters, and the coding
// schemes §34.5.9.2 lists either break their own output into lines or tolerate
// a reader that does. A test showing a reading takes a block whichever way it
// arrives writes the envelope with the tool and then breaks the block by hand,
// so the two texts differ in the breaks and in nothing else.

// The same text with the line standing after `opening` broken into `pieces`
// lines of as near the same length as divides. A text that does not write
// `opening`, or that writes nothing under it, comes back unchanged.
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
