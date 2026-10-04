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

  // `loc` restated in the source it came from, or `loc` unchanged when it
  // stands in a file the user wrote. One hop answers it, because an origin
  // names a real source file and a real source file has no origins of its own.
  SourceLoc ResolveToOrigin(SourceLoc loc) const;

  // §37.3.6: an object is protected when it represents code contained in a
  // decryption envelope. The text a reading recovers from an envelope is
  // registered as a source of its own and marked here, and a position is
  // protected when it stands in, or comes from, a source so marked.
  void MarkProtected(uint32_t file_id);
  bool IsProtected(SourceLoc loc) const;

  // The id the most recently registered source was given, and 0 before any.
  uint32_t LastFileId() const { return static_cast<uint32_t>(files_.size()); }

  // §34.5.32.2: the viewports of the envelopes a reading closed, in the order
  // it closed them, for the stages that resolve the objects they
  // name and grant the access they ask.
  void AddViewport(EnvelopeViewport viewport);
  const std::vector<EnvelopeViewport>& Viewports() const { return viewports_; }

  // Drops the viewports `stale` answers true for, which describe envelopes of
  // code that is no longer part of the design.
  void DropViewports(const std::function<bool(const EnvelopeViewport&)>& stale);

  // Whether `loc` stands in, or comes from, the text of the envelope
  // `viewport` describes.
  bool StandsInEnvelope(SourceLoc loc, const EnvelopeViewport& viewport) const;

 private:
  struct FileEntry {
    std::string path;
    std::string content;
    std::vector<uint32_t> line_offsets;
    // Empty unless this entry is preprocessed text, in which case it holds one
    // entry per line of it.
    std::vector<OutputLineOrigin> line_origins;
    bool is_protected = false;
  };

  void ComputeLineOffsets(FileEntry& entry);

  // A deque, not a vector: FileContent() hands out string_views into
  // FileEntry::content (and Token::text retains them). A vector would relocate
  // every FileEntry when it grows, so a short content held inline by the
  // std::string small-string optimization would move and dangle those views on
  // the next AddFile. A deque never relocates existing elements on push_back.
  std::deque<FileEntry> files_;
  std::vector<EnvelopeViewport> viewports_;
};

}  // namespace delta
