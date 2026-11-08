#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <initializer_list>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_diagnosed.h"
#include "helpers_config_reports.h"
#include "lexer/lexer.h"
#include "parser/library_map.h"
#include "parser/parser.h"

using namespace delta;

struct ConfigUnit {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  Diagnosed diagnosed{diag};
  CompilationUnit* cu = nullptr;

  bool Parse(const std::string& src) {
    auto fid = mgr.AddFile("<test>", src);
    Lexer lexer(mgr.FileContent(fid), fid, diag);
    Parser parser(lexer, arena, diag);
    cu = parser.Parse();
    return cu != nullptr && !diag.HasErrors();
  }

  void PlaceModulesInLibraries(std::initializer_list<const char*> libraries) {
    ASSERT_EQ(cu->modules.size(), libraries.size());
    size_t i = 0;
    for (const char* library : libraries) cu->modules[i++]->library = library;
    PlaceConfigsWithTheirTops(cu);
  }

  void PlaceConfigInLibrary(std::string_view library) {
    ASSERT_EQ(cu->configs.size(), 1u);
    cu->configs[0]->library = library;
  }

  RtlirDesign* ElaborateTop(std::string_view top) {
    Elaborator elab(arena, diag, cu);
    return elab.Elaborate(top);
  }

  RtlirDesign* ElaborateConfig(size_t index) {
    Elaborator elab(arena, diag, cu);
    return elab.Elaborate(cu->configs[index]);
  }
};

inline RtlirModule* SoleTopModule(RtlirDesign* design) {
  if (design == nullptr || design->top_modules.empty()) return nullptr;
  return design->top_modules[0];
}

inline void ExpectChainBindsChildAndLeaf(RtlirDesign* design,
                                         std::string_view child_name,
                                         std::string_view child_library,
                                         std::string_view leaf_library) {
  auto* top = SoleTopModule(design);
  ASSERT_NE(top, nullptr);
  ASSERT_EQ(top->children.size(), 1u);
  auto* child = top->children[0].resolved;
  ASSERT_NE(child, nullptr);
  EXPECT_EQ(child->name, child_name);
  EXPECT_EQ(child->library, child_library);
  ASSERT_EQ(child->children.size(), 1u);
  auto* leaf = child->children[0].resolved;
  ASSERT_NE(leaf, nullptr);
  EXPECT_EQ(leaf->library, leaf_library);
}

struct MappedConfigUnit : ConfigUnit {
  LibraryMap lib_map;

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

  std::string_view ConfigLibrary() const { return cu->configs[0]->library; }
};
