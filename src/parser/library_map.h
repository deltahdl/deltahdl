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
class SourceManager;

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

  // The library a file belongs to: the one whose declaration claims the file
  // most specifically, "work" where no declaration claims it, and an empty
  // name where several claim it equally and there is no one library to name.
  std::string_view LibraryForFile(std::string_view path) const;

  // Every library claiming a file as specifically as any other does, in
  // declaration order and no library named twice. A caller reporting the
  // ambiguity LibraryForFile answers with an empty name reads the names of the
  // libraries it is between from here.
  std::vector<std::string_view> LibrariesForFile(std::string_view path) const;

  // Where the first of the declarations claiming a file as specifically as any
  // other stands, which is the `library` keyword that opens it. A caller
  // reporting the ambiguity LibraryForFile answers with an empty name stands
  // its report there. Every one of those declarations claims the file equally,
  // so none of them is the breach on its own, and the first is the one a
  // reader of the map file reaches first. The answer is SourceLoc::None()
  // where no declaration claims the file, and where the declarations were read
  // without a SourceManager to resolve a position against.
  SourceLoc FirstDeclarationClaiming(std::string_view path) const;

  static bool PathMatches(std::string_view spec, std::string_view base_dir,
                          std::string_view path);

  // The path a file path specification names, with the directory a relative
  // one is resolved from supplied by `base_dir` and any parent and
  // current-directory steps taken. A specification written between double
  // quotes names the same path as the bare spelling of it: the surrounding
  // pair delimits the path rather than belonging to it.
  static std::string ResolveSpec(std::string_view raw_spec,
                                 std::string_view base_dir);

  // Parse every map file loaded from here on into `mgr`, so that a position
  // this map hands back names a file `mgr` holds. A caller that reports
  // through a DiagEngine built over `mgr` calls this before LoadMapFile,
  // because a file identifier means something only to the manager that issued
  // it. A map given no manager parses each map file into a manager of its own,
  // and keeps no position from what it read there.
  void ResolvePositionsAgainst(SourceManager& mgr);

  bool LoadMapFile(const std::filesystem::path& map_file,
                   std::vector<std::string>* errors = nullptr);

  void TagCompilationUnit(CompilationUnit& cu,
                          std::string_view source_path) const;

  std::vector<std::string_view> LibraryDeclarationOrder() const;

  // Whether `name` is a library name. A library declaration introduces its
  // library with an identifier, so a name is a letter or an underscore
  // followed by letters, digits, underscores and dollar signs; anything else
  // -- a file name, a path, a wildcard, a whole definition -- is not something
  // a declaration could have named.
  static bool IsLibraryName(std::string_view name);

  // The library search order an invocation is to use: an ordered list of
  // library names, no name repeated.
  //
  // `cli_override` holds the library names an invocation specified for itself,
  // in the order it specified them. Those come first, ahead of the order the
  // declarations in this map establish. Every library this map declares that
  // the override passed over then follows, in declaration order, so an
  // override decides only as much as it names and the declarations still rank
  // the rest. An empty override therefore yields the declaration order alone.
  //
  // An override entry names a library and nothing more: what each named
  // library is defined to hold is this map's business, so a name that no
  // declaration here introduced ranks a library that holds nothing. An entry
  // that is not a library name at all is left out of the returned order and
  // described in `errors` when a vector is passed.
  std::vector<std::string> ResolveSearchOrder(
      const std::vector<std::string>& cli_override,
      std::vector<std::string>* errors = nullptr) const;

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
    // Where the declaration this specification was written in stands, so that
    // a report about the claim it makes can be given that position.
    SourceLoc loc;
  };
  std::vector<Entry> entries_;
  std::unordered_map<std::string, LibraryCell> cells_;
  SourceManager* mgr_ = nullptr;

  // Every specification claiming a file as specifically as any other does, in
  // declaration order, one element per specification rather than per library.
  // The names of the libraries and the position of the first declaration are
  // each read off this, so the rule that ranks an explicit file name above a
  // wildcarded one above a directory is applied in one place.
  std::vector<const Entry*> EntriesClaiming(std::string_view path) const;

  bool LoadMapFileImpl(const std::filesystem::path& map_file,
                       std::vector<std::filesystem::path>& stack,
                       std::vector<std::string>* errors);
};

}  // namespace delta
