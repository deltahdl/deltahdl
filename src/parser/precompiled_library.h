#pragma once

#include <filesystem>
#include <string_view>

namespace delta {

class Arena;
class DiagEngine;
class SourceManager;
struct CompilationUnit;

// Persistent on-disk library used by the separate-compilation-tool
// strategy of IEEE 1800-2023 §33.5.3.  The format is tool-specific (the
// LRM leaves it open) and the file lives wherever the caller asks; the
// only invariants the standard imposes are that the form survives
// across compiler invocations and is sufficient for the binding tool to
// descend the design hierarchy from a named top.
class PrecompiledLibrary {
 public:
  // Parse `source` to confirm it compiles, then append a chunk holding
  // the source bytes and `library` tag to the file at `path`.  The
  // first call creates the file and writes a magic header; subsequent
  // calls append, so a library can be built up across one or more
  // invocations of the compiler tool.  Returns false when `source`
  // does not parse cleanly or the file cannot be written.
  static bool Save(std::string_view source, std::string_view library,
                   const std::filesystem::path& path);

  // Read every chunk written to `path` and append the reconstructed
  // cell descriptions to `target`, tagged with the library each chunk
  // recorded at Save time.  The reconstructed cells are byte-for-byte
  // re-parsed so the binding tool sees the same AST shape it would
  // have seen by parsing the original source file directly.  Returns
  // false on missing file, missing or wrong magic header, truncated
  // chunk, or a re-parse error.
  static bool Load(const std::filesystem::path& path,
                   CompilationUnit& target, SourceManager& mgr,
                   Arena& arena, DiagEngine& diag);
};

}  // namespace delta
