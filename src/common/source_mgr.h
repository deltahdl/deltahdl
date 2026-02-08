#pragma once

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

  std::vector<FileEntry> files_;
};

}  // namespace delta
