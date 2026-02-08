#pragma once

#include "common/source_loc.h"

#include <string>
#include <string_view>
#include <vector>

namespace delta {

class SourceManager {
  public:
    uint32_t add_file(std::string path, std::string content);

    std::string_view file_path(uint32_t file_id) const;
    std::string_view file_content(uint32_t file_id) const;

    std::string format_loc(SourceLoc loc) const;
    std::string_view get_line_text(SourceLoc loc) const;

    size_t file_count() const { return files_.size(); }

  private:
    struct FileEntry {
        std::string path;
        std::string content;
        std::vector<uint32_t> line_offsets;
    };

    void compute_line_offsets(FileEntry& entry);

    std::vector<FileEntry> files_;
};

} // namespace delta
