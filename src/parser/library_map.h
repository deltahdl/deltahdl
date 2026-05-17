#pragma once

#include <filesystem>
#include <string>
#include <string_view>
#include <vector>

namespace delta {

struct CompilationUnit;
struct LibraryDecl;

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

 private:
  struct Entry {
    std::string library;
    std::string base_dir;
    std::string spec;
  };
  std::vector<Entry> entries_;

  bool LoadMapFileImpl(const std::filesystem::path& map_file,
                       std::vector<std::filesystem::path>& stack,
                       std::vector<std::string>* errors);
};

}
