#pragma once

#include <deque>
#include <string>
#include <string_view>
#include <vector>

#include "common/source_loc.h"

namespace delta {

class SourceManager {
 public:
  uint32_t AddFile(std::string path, std::string content);

  // Registers preprocessed text, whose lines are the lines of no file the user
  // wrote. `line_origins` names the source of each of them, so a position in
  // this text is reported as the position in the source it came from. A caller
  // that has no such table uses AddFile above and gets positions in the text as
  // it registered it.
  uint32_t AddPreprocessedFile(std::string path, std::string content,
                               std::vector<OutputLineOrigin> line_origins);

  std::string_view FilePath(uint32_t file_id) const;
  std::string_view FileContent(uint32_t file_id) const;

  // Where `loc` stands in the source somebody wrote, as `path:line:column`.
  // A position in preprocessed text registered with its origins is answered for
  // by the file and line it came from; every other position is answered for as
  // it stands. The column is not translated either way, because a macro
  // expanded into a line moves the columns after it and no record of that is
  // kept.
  std::string FormatLoc(SourceLoc loc) const;

  // The text of the line `loc` stands on, taken from the source it came from
  // for a position that has an origin.
  std::string_view GetLineText(SourceLoc loc) const;

 private:
  struct FileEntry {
    std::string path;
    std::string content;
    std::vector<uint32_t> line_offsets;
    // Empty unless this entry is preprocessed text, in which case it holds one
    // entry per line of it.
    std::vector<OutputLineOrigin> line_origins;
  };

  // `loc` restated in the source it came from, or `loc` unchanged when it
  // stands in a file the user wrote. One hop answers it, because an origin
  // names a real source file and a real source file has no origins of its own.
  SourceLoc ResolveToOrigin(SourceLoc loc) const;

  void ComputeLineOffsets(FileEntry& entry);

  // A deque, not a vector: FileContent() hands out string_views into
  // FileEntry::content (and Token::text retains them). A vector would relocate
  // every FileEntry when it grows, so a short content held inline by the
  // std::string small-string optimization would move and dangle those views on
  // the next AddFile. A deque never relocates existing elements on push_back.
  std::deque<FileEntry> files_;
};

}  // namespace delta
