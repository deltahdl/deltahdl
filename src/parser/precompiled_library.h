#pragma once

#include <filesystem>
#include <string_view>

namespace delta {

class Arena;
class DiagEngine;
class SourceManager;
struct CompilationUnit;

// A file holding compiled cells, in a format and at a location this tool
// chooses for itself. Compiling a source description writes the cells it
// declares into such a file under a library name; a later run of this or any
// other tool reads them back without the source description being available to
// it, which is the point of keeping them.
//
// The file accumulates: each compile appends a record to it, so the cells of a
// design may be written by as many separate compiles as suits the caller, into
// one file or several, under one library name or several.
class PrecompiledLibrary {
 public:
  // Compiles `source` into library `library`, adding its cells to the file at
  // `path` and creating that file if it is not there yet.
  //
  // Returns false, having written nothing that outlasts the call, when the
  // library name is empty (cells must go into some library), when the source
  // description does not parse, or when the file cannot be written. That last
  // case leaves the file exactly as long as it was: cells earlier compiles put
  // there stay readable rather than being lost behind a half-written record.
  // A true return means the record is in the filesystem, not merely handed to
  // the stream.
  static bool Save(std::string_view source, std::string_view library,
                   const std::filesystem::path& path);

  // Reads every cell held at `path` into `target`, tagging each with the
  // library name it was compiled under. Cells are added to whatever `target`
  // already holds, so several files can be read into one unit.
  //
  // Returns false when `path` is not a file this tool wrote, when a record in
  // it is damaged, or when a source description in it no longer parses.
  static bool Load(const std::filesystem::path& path, CompilationUnit& target,
                   SourceManager& mgr, Arena& arena, DiagEngine& diag);
};

}  // namespace delta
