#include "common/source_mgr.h"

#include <format>

namespace delta {

uint32_t SourceManager::AddFile(std::string path, std::string content) {
  uint32_t id = static_cast<uint32_t>(files_.size()) + 1;
  FileEntry entry{std::move(path), std::move(content), {}, {}};
  ComputeLineOffsets(entry);
  files_.push_back(std::move(entry));
  return id;
}

uint32_t SourceManager::AddPreprocessedFile(
    std::string path, std::string content,
    std::vector<OutputLineOrigin> line_origins) {
  uint32_t id = static_cast<uint32_t>(files_.size()) + 1;
  FileEntry entry{
      std::move(path), std::move(content), {}, std::move(line_origins)};
  ComputeLineOffsets(entry);
  files_.push_back(std::move(entry));
  return id;
}

SourceLoc SourceManager::ResolveToOrigin(SourceLoc loc) const {
  if (loc.file_id == 0 || loc.file_id > files_.size()) return loc;
  const auto& origins = files_[loc.file_id - 1].line_origins;
  // The last line of the text is the empty one after its final newline, which
  // no source line wrote, so a position can stand one line past the table.
  if (loc.line == 0 || loc.line > origins.size()) return loc;
  const auto& origin = origins[loc.line - 1];
  if (origin.file_id == 0) return loc;
  return SourceLoc{origin.file_id, origin.line, loc.column};
}

std::string_view SourceManager::FilePath(uint32_t file_id) const {
  if (file_id == 0 || file_id > files_.size()) {
    return "<unknown>";
  }
  return files_[file_id - 1].path;
}

std::string_view SourceManager::FileContent(uint32_t file_id) const {
  if (file_id == 0 || file_id > files_.size()) {
    return "";
  }
  return files_[file_id - 1].content;
}

std::string SourceManager::FormatLoc(SourceLoc loc) const {
  if (!loc.IsValid()) {
    return "<unknown location>";
  }
  auto at = ResolveToOrigin(loc);
  auto path = FilePath(at.file_id);
  return std::format("{}:{}:{}", path, at.line, at.column);
}

std::string_view SourceManager::GetLineText(SourceLoc where) const {
  auto loc = ResolveToOrigin(where);
  if (loc.file_id == 0 || loc.file_id > files_.size()) {
    return "";
  }
  const auto& entry = files_[loc.file_id - 1];
  if (loc.line == 0 || loc.line > entry.line_offsets.size()) {
    return "";
  }
  uint32_t start = entry.line_offsets[loc.line - 1];
  uint32_t end = (loc.line < entry.line_offsets.size())
                     ? entry.line_offsets[loc.line]
                     : static_cast<uint32_t>(entry.content.size());
  while (end > start &&
         (entry.content[end - 1] == '\n' || entry.content[end - 1] == '\r')) {
    --end;
  }
  return std::string_view(entry.content).substr(start, end - start);
}

void SourceManager::ComputeLineOffsets(FileEntry& entry) {
  entry.line_offsets.push_back(0);
  for (uint32_t i = 0; i < entry.content.size(); ++i) {
    if (entry.content[i] == '\n') {
      entry.line_offsets.push_back(i + 1);
    }
  }
}

}  // namespace delta
