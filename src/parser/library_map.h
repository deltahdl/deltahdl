#pragma once

#include <filesystem>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/source_loc.h"

namespace delta {

class Arena;
struct CompilationUnit;
struct ConfigDecl;
struct LibraryDecl;
class DiagEngine;
class SourceManager;

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

  std::vector<std::string_view> LibrariesForFile(std::string_view path) const;

  SourceLoc FirstDeclarationClaiming(std::string_view path) const;

  static bool PathMatches(std::string_view spec, std::string_view base_dir,
                          std::string_view path);

  static std::string ResolveSpec(std::string_view raw_spec,
                                 std::string_view base_dir);

  void ResolvePositionsAgainst(SourceManager& mgr);

  bool LoadMapFile(const std::filesystem::path& map_file,
                   std::vector<std::string>* errors = nullptr);

  void TagCompilationUnit(CompilationUnit& cu,
                          std::string_view source_path) const;

  std::vector<std::string_view> LibraryDeclarationOrder() const;

  std::vector<ConfigDecl*> DeclaredConfigs() const;

  static bool IsLibraryName(std::string_view name);

  std::vector<std::string> ResolveSearchOrder(
      const std::vector<std::string>& cli_override,
      std::vector<std::string>* errors = nullptr) const;

  void WriteCell(std::string_view library, std::string_view name,
                 bool is_module, SourceLoc loc, DiagEngine& diag);

  const LibraryCell* CellInLibrary(std::string_view library,
                                   std::string_view name) const;

  void BeginNewInvocation();

 private:
  struct Entry {
    std::string library;
    std::string base_dir;
    std::string spec;
    SourceLoc loc;
  };
  std::vector<Entry> entries_;
  std::unordered_map<std::string, LibraryCell> cells_;
  SourceManager* mgr_ = nullptr;
  std::shared_ptr<SourceManager> own_mgr_;
  std::vector<std::shared_ptr<Arena>> arenas_;
  std::vector<std::pair<ConfigDecl*, std::string>> map_configs_;

  std::vector<const Entry*> EntriesClaiming(std::string_view path) const;

  bool LoadMapFileImpl(const std::filesystem::path& map_file,
                       std::vector<std::filesystem::path>& stack,
                       std::vector<std::string>* errors);

  bool LoadDescriptionsInOrder(const CompilationUnit& cu,
                               const std::filesystem::path& canon,
                               std::vector<std::filesystem::path>& stack,
                               std::vector<std::string>* errors);
};

}  // namespace delta
