#pragma once

#include <cstdint>
#include <deque>
#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "common/envelope_viewport.h"
#include "common/source_loc.h"

namespace delta {

class SourceManager {
 public:
  uint32_t AddFile(std::string path, std::string content);

  uint32_t AddPreprocessedFile(std::string path, std::string content,
                               std::vector<OutputLineOrigin> line_origins);

  std::string_view FilePath(uint32_t file_id) const;
  std::string_view FileContent(uint32_t file_id) const;

  std::string FormatLoc(SourceLoc loc) const;

  std::string_view GetLineText(SourceLoc loc) const;

  SourceLoc ResolveToOrigin(SourceLoc loc) const;

  void MarkProtected(uint32_t file_id);
  bool IsProtected(SourceLoc loc) const;

  uint32_t LastFileId() const { return static_cast<uint32_t>(files_.size()); }

  void AddViewport(EnvelopeViewport viewport);
  const std::vector<EnvelopeViewport>& Viewports() const { return viewports_; }

  void DropViewports(const std::function<bool(const EnvelopeViewport&)>& stale);

  bool StandsInEnvelope(SourceLoc loc, const EnvelopeViewport& viewport) const;

 private:
  struct FileEntry {
    std::string path;
    std::string content;
    std::vector<uint32_t> line_offsets;
    std::vector<OutputLineOrigin> line_origins;
    bool is_protected = false;
  };

  void ComputeLineOffsets(FileEntry& entry);

  std::deque<FileEntry> files_;
  std::vector<EnvelopeViewport> viewports_;
};

}  // namespace delta
