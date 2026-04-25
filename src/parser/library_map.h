#pragma once

#include <filesystem>
#include <string>
#include <string_view>
#include <vector>

namespace delta {

struct CompilationUnit;
struct LibraryDecl;

// Maps source files to libraries per IEEE 1800-2023 §33.3.1.
//
// AddDeclaration registers a parsed library_declaration with the directory
// of the .map file it came from; declarations are kept in insertion order
// so that multiple .map files specified on the command line take effect in
// the order they were processed.  LibraryForFile walks the table and
// returns the first matching library, or "work" when nothing matches.
class LibraryMap {
 public:
  void AddDeclaration(const LibraryDecl& decl, std::string_view base_dir);

  std::string_view LibraryForFile(std::string_view path) const;

  // Test whether `path` is matched by `spec` interpreted relative to
  // `base_dir`.  Public so callers and tests can probe single-spec
  // matching directly.
  static bool PathMatches(std::string_view spec, std::string_view base_dir,
                          std::string_view path);

  // Resolve the literal path of `spec` against `base_dir`, applying the
  // §33.3.1 trailing-slash rule and `.`/`..` segment normalization.  The
  // wildcard characters `?`, `*`, and `...` are preserved in the result.
  static std::string ResolveSpec(std::string_view spec,
                                 std::string_view base_dir);

  // Read a lib.map file from disk, register its library declarations,
  // and recursively expand any include statements per §33.3.2.  Relative
  // paths in both library and include statements anchor to the directory
  // of the file that contains them.  Returns true on success; on
  // failure, diagnostic messages are appended to `errors` (if non-null)
  // and the call returns false.  Cycles between map files are detected
  // and reported instead of looping.
  bool LoadMapFile(const std::filesystem::path& map_file,
                   std::vector<std::string>* errors = nullptr);

  // §33.3.3: stamp every cell-kind design element in `cu` (modules,
  // interfaces, programs, primitives, packages, configs) with the
  // library that owns `source_path` according to LibraryForFile.  The
  // returned view's storage is owned by this LibraryMap, so the CU must
  // not outlive it.
  void TagCompilationUnit(CompilationUnit& cu,
                          std::string_view source_path) const;

  // §33.6.1: list the libraries in declaration order, deduplicated by
  // first appearance.  The default-binding rule searches libraries in
  // this order to pick a cell when no configuration is in use.  The
  // returned views are owned by this LibraryMap.
  std::vector<std::string_view> LibraryDeclarationOrder() const;

  // §33.8.1: resolve the effective library search order for default
  // binding when no configuration is in use.  When `cli_override` is
  // non-empty, it overrides the lib.map's declaration order verbatim;
  // the override carries library names only, so the definitions still
  // come from the entries this LibraryMap was loaded with.  When the
  // override is empty, the lib.map's declaration order is returned
  // unchanged.
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

}  // namespace delta
