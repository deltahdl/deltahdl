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

  std::string_view FilePath(uint32_t file_id) const;
  std::string_view FileContent(uint32_t file_id) const;

  std::string FormatLoc(SourceLoc loc) const;
  std::string_view GetLineText(SourceLoc loc) const;

 private:
  struct FileEntry {
    std::string path;
    std::string content;
    std::vector<uint32_t> line_offsets;
  };

  void ComputeLineOffsets(FileEntry& entry);

  // A deque, not a vector: FileContent() hands out string_views into
  // FileEntry::content (and Token::text retains them). A vector would relocate
  // every FileEntry when it grows, so a short content held inline by the
  // std::string small-string optimization would move and dangle those views on
  // the next AddFile. A deque never relocates existing elements on push_back.
  std::deque<FileEntry> files_;
};

}  // namespace delta
