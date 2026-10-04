#pragma once

#include <cstdint>
#include <filesystem>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "preprocessor/protect_license.h"

namespace delta {

class Arena;
class DiagEngine;
class SourceManager;
struct CompilationUnit;

// What a compile records beside the text of a source description: the
// directive state the preprocessor carried to each design element's header --
// its `timescale (§3.14.2.3), default net type and the rest (§22) -- and the
// modules `celldefine marked (§22.10). A binding run reads no source
// description and runs no preprocessor, so it applies these to the cells as
// the compile that preprocessed the text applied them.
//
// Beside them go the runtime licences the preprocessor met in the text's
// encrypted models. §34.5.29.2 has each asked before the model is executed,
// and a precompiled model is executed by the binding run, not by the compile
// that decrypted it.
//
// And the lines of the text that came out of a decryption envelope, numbered
// from 1: §37.3.6 makes the objects of that code protected in whichever run
// executes it.
struct PrecompiledDirectives {
  std::vector<ModuleDirectives> modules;
  std::vector<std::string> cell_modules;
  std::vector<ProtectLicense> runtime_licenses;
  std::vector<uint32_t> protected_lines;
};

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
  // Compiles `source`, the text the preprocessor produced for a source
  // description, into library `library` with the directive state `directives`
  // recorded beside it, adding its cells to the file at `path` and creating
  // that file if it is not there yet. Nothing is reported: a caller that wants
  // the parse errors of the source parses it itself first.
  //
  // Returns false, having written nothing that outlasts the call, when the
  // library name is empty (cells must go into some library), when the source
  // description does not parse, or when the file cannot be written. That last
  // case leaves the file exactly as long as it was: cells earlier compiles put
  // there stay readable rather than being lost behind a half-written record.
  // A true return means the record is in the filesystem, not merely handed to
  // the stream.
  static bool Save(std::string_view source, std::string_view library,
                   const std::filesystem::path& path,
                   const PrecompiledDirectives& directives = {});

  // The names of the cells `source` declares in the definitions name space --
  // modules, interfaces, programs, checkers, primitives and configurations --
  // in the order it declares them; none where it does not parse. Nothing is
  // reported.
  static std::vector<std::string> CellNames(std::string_view source);

  // Reads every cell held at `path` into `target`, tagging each with the
  // library name it was compiled under. Cells are added to whatever `target`
  // already holds, so several files can be read into one unit.
  //
  // Returns false when `path` is not a file this tool wrote, when a record in
  // it is damaged, or when a source description in it no longer parses.
  static bool Load(const std::filesystem::path& path, CompilationUnit& target,
                   SourceManager& mgr, Arena& arena, DiagEngine& diag);

  // The runtime licences every record held at `path` states, in the order the
  // records were written; none where `path` is not a file this tool wrote or a
  // record in it is damaged, which Load reports as no cells read.
  static std::vector<ProtectLicense> RuntimeLicenses(
      const std::filesystem::path& path);
};

}  // namespace delta
