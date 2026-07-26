#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <initializer_list>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/library_map.h"
#include "parser/parser.h"

using namespace delta;

// A compilation unit parsed for a test about a config declaration.
//
// A config's rules are read at elaboration, so a test states them as real
// source and then elaborates -- either a module by name, or the config itself.
// The library each cell lives in is the other half of what a config resolves
// against, and a single merged compilation unit carries one library tag, so a
// test that needs like-named cells in different libraries assigns them here
// rather than routing every one through a lib.map.
struct ConfigUnit {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  CompilationUnit* cu = nullptr;

  // Parses `src`. Returns false when it does not parse or when parsing raised
  // a diagnostic, so a test asserts on the result before reading the unit.
  bool Parse(const std::string& src) {
    auto fid = mgr.AddFile("<test>", src);
    Lexer lexer(mgr.FileContent(fid), fid, diag);
    Parser parser(lexer, arena, diag);
    cu = parser.Parse();
    return cu != nullptr && !diag.HasErrors();
  }

  // Puts each module in the library at the same position of `libraries`, in
  // declaration order.
  void PlaceModulesInLibraries(std::initializer_list<const char*> libraries) {
    ASSERT_EQ(cu->modules.size(), libraries.size());
    size_t i = 0;
    for (const char* library : libraries) cu->modules[i++]->library = library;
  }

  // Puts the unit's one config in `library`, for a test whose subject is not
  // where that library came from.
  void PlaceConfigInLibrary(std::string_view library) {
    ASSERT_EQ(cu->configs.size(), 1u);
    cu->configs[0]->library = std::string(library);
  }

  // Elaborates the design element `top` names, and whether the elaboration
  // raised a diagnostic is read off `diag` afterwards.
  RtlirDesign* ElaborateTop(std::string_view top) {
    Elaborator elab(arena, diag, cu);
    return elab.Elaborate(std::string(top));
  }

  // Elaborates from the config at `index` instead of from a module name, which
  // is what puts the config's own rules in force over the hierarchy.
  RtlirDesign* ElaborateConfig(size_t index) {
    Elaborator elab(arena, diag, cu);
    return elab.Elaborate(cu->configs[index]);
  }
};

// The one top module an elaborated design holds, or nullptr when it holds
// none.
inline RtlirModule* SoleTopModule(RtlirDesign* design) {
  if (design == nullptr || design->top_modules.empty()) return nullptr;
  return design->top_modules[0];
}

// The same, for a test whose subject is the library a config carries rather
// than the rules inside it. A config's library is not intrinsic to its own
// syntax: §33.3.3 assigns it from the source file's path through a real
// lib.map, so the file and the map both go on disk and the tag is read back
// off the unit rather than written onto it.
struct MappedConfigUnit : ConfigUnit {
  LibraryMap lib_map;

  // Loads `map_text` as the library map and parses `src` as a file the map
  // covers, then tags the unit the way the map machinery does. `dir` supplies
  // the directory both files are written into, since the map resolver anchors
  // a relative library spec to the map file's own directory. Returns false
  // when the map does not load or the source does not parse.
  template <typename ScratchDirT>
  bool ParseUnderMap(ScratchDirT& dir, const std::string& map_text,
                     const std::string& src) {
    auto map_file = dir.Write("lib.map", map_text);
    auto path = dir.Write("top.v", src);
    if (!lib_map.LoadMapFile(map_file)) return false;
    auto fid = mgr.AddFile(path.string(), src);
    Lexer lexer(mgr.FileContent(fid), fid, diag);
    Parser parser(lexer, arena, diag);
    cu = parser.Parse();
    if (cu == nullptr || diag.HasErrors()) return false;
    lib_map.TagCompilationUnit(*cu, path.string());
    return true;
  }

  // The library the map assigned the unit's one config.
  const std::string& ConfigLibrary() const { return cu->configs[0]->library; }
};
