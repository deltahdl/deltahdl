#pragma once

#include <filesystem>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/source_loc.h"

namespace delta {

struct CompilationUnit;
struct LibraryDecl;
class DiagEngine;

// A design element (cell) that has been written into a library. Tracks whether
// the cell was written during the current compiler invocation so that a later
// write of the same name can be distinguished as a single-invocation duplicate
// (a likely mistake) versus a separate-compile recompile.
struct LibraryCell {
  std::string library;
  std::string name;
  bool is_module = false;
  SourceLoc loc;
  bool from_current_invocation = true;
};

class LibraryMap {
 public:
  void AddDeclaration(const LibraryDecl& decl, std::string_view base_dir);

  std::string_view LibraryForFile(std::string_view path) const;

  static bool PathMatches(std::string_view spec, std::string_view base_dir,
                          std::string_view path);

  static std::string ResolveSpec(std::string_view spec,
                                 std::string_view base_dir);

  bool LoadMapFile(const std::filesystem::path& map_file,
                   std::vector<std::string>* errors = nullptr);

  void TagCompilationUnit(CompilationUnit& cu,
                          std::string_view source_path) const;

  std::vector<std::string_view> LibraryDeclarationOrder() const;

  std::vector<std::string> ResolveSearchOrder(
      const std::vector<std::string>& cli_override) const;

  // §33.3.1.1: write a cell of the given name into its mapped library. The most
  // recently encountered cell of a name replaces any earlier cell of that name
  // in the same library. When a module cell collides with a module of the same
  // name already written to that library during the current invocation, a
  // warning is issued; the new cell still replaces the old one.
  void WriteCell(std::string_view library, std::string_view name,
                 bool is_module, SourceLoc loc, DiagEngine& diag);

  // Returns the cell currently written under the given name in the library, or
  // nullptr if no such cell has been written.
  const LibraryCell* CellInLibrary(std::string_view library,
                                   std::string_view name) const;

  // Marks the writes accumulated so far as belonging to a prior invocation, so
  // that a subsequent write of the same name is treated as a recompile rather
  // than a single-invocation duplicate.
  void BeginNewInvocation();

 private:
  struct Entry {
    std::string library;
    std::string base_dir;
    std::string spec;
  };
  std::vector<Entry> entries_;
  std::unordered_map<std::string, LibraryCell> cells_;

  bool LoadMapFileImpl(const std::filesystem::path& map_file,
                       std::vector<std::filesystem::path>& stack,
                       std::vector<std::string>* errors);
};

}  // namespace delta
