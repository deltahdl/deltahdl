#include <gtest/gtest.h>

#include "parser/ast.h"
#include "parser/library_map.h"

using namespace delta;

namespace {

LibraryDecl MakeLibDecl(std::string_view name,
                        std::initializer_list<std::string_view> paths) {
  LibraryDecl d;
  d.name = name;
  for (auto p : paths) d.file_paths.push_back(p);
  return d;
}

// §33.3.3: a module's library is the library whose file_path_spec
// matches the source file's path.
TEST(LibraryMapCellTagging, TagsModuleWithMatchingLibrary) {
  LibraryMap m;
  m.AddDeclaration(MakeLibDecl("rtlLib", {"*.v"}), "/proj/rtl");

  CompilationUnit cu;
  ModuleDecl mod;
  mod.name = "top";
  cu.modules.push_back(&mod);

  m.TagCompilationUnit(cu, "/proj/rtl/top.v");
  EXPECT_EQ(mod.library, "rtlLib");
}

// §33.3.3 + §33.3.1 work-default: a source not matched by any library
// is tagged with "work".
TEST(LibraryMapCellTagging, TagsUnmatchedSourceWithWork) {
  LibraryMap m;
  m.AddDeclaration(MakeLibDecl("rtlLib", {"*.v"}), "/proj/rtl");

  CompilationUnit cu;
  ModuleDecl mod;
  mod.name = "elsewhere";
  cu.modules.push_back(&mod);

  m.TagCompilationUnit(cu, "/elsewhere/top.sv");
  EXPECT_EQ(mod.library, "work");
}

// All §33.2.1 cell kinds (module, primitive, interface, program,
// package, configuration) are tagged.  Classes are intentionally
// excluded because §33.2.1 does not list them as cells.
TEST(LibraryMapCellTagging, TagsAllCellKinds) {
  LibraryMap m;
  m.AddDeclaration(MakeLibDecl("L", {"*.v"}), "/proj");

  CompilationUnit cu;

  ModuleDecl mod;
  mod.decl_kind = ModuleDeclKind::kModule;
  cu.modules.push_back(&mod);

  ModuleDecl ifc;
  ifc.decl_kind = ModuleDeclKind::kInterface;
  cu.interfaces.push_back(&ifc);

  ModuleDecl prog;
  prog.decl_kind = ModuleDeclKind::kProgram;
  cu.programs.push_back(&prog);

  UdpDecl udp;
  cu.udps.push_back(&udp);

  PackageDecl pkg;
  cu.packages.push_back(&pkg);

  ConfigDecl cfg;
  cu.configs.push_back(&cfg);

  m.TagCompilationUnit(cu, "/proj/x.v");

  EXPECT_EQ(mod.library, "L");
  EXPECT_EQ(ifc.library, "L");
  EXPECT_EQ(prog.library, "L");
  EXPECT_EQ(udp.library, "L");
  EXPECT_EQ(pkg.library, "L");
  EXPECT_EQ(cfg.library, "L");
}

// §33.3.3 + §33.3.1.1 ambiguity: when LibraryForFile returns the empty
// ambiguity sentinel, that empty string is what the cells receive.
// This lets a downstream driver detect that no unique library was
// determined and report the §33.3.1.1 error.
TEST(LibraryMapCellTagging, AmbiguousMatchPropagatesEmptyTag) {
  LibraryMap m;
  m.AddDeclaration(MakeLibDecl("a", {"*.v"}), "/proj");
  m.AddDeclaration(MakeLibDecl("b", {"*.v"}), "/proj");

  CompilationUnit cu;
  ModuleDecl mod;
  cu.modules.push_back(&mod);

  m.TagCompilationUnit(cu, "/proj/x.v");
  EXPECT_TRUE(mod.library.empty());
}

// Tagging two compilation units from different source paths writes
// different libraries to each — confirms each tag call is independent.
TEST(LibraryMapCellTagging, IndependentTaggingPerCompilationUnit) {
  LibraryMap m;
  m.AddDeclaration(MakeLibDecl("rtl", {"*.v"}), "/proj");
  m.AddDeclaration(MakeLibDecl("gates", {"*.vg"}), "/proj");

  CompilationUnit cu_rtl;
  ModuleDecl mod_rtl;
  cu_rtl.modules.push_back(&mod_rtl);

  CompilationUnit cu_gates;
  ModuleDecl mod_gates;
  cu_gates.modules.push_back(&mod_gates);

  m.TagCompilationUnit(cu_rtl, "/proj/top.v");
  m.TagCompilationUnit(cu_gates, "/proj/top.vg");

  EXPECT_EQ(mod_rtl.library, "rtl");
  EXPECT_EQ(mod_gates.library, "gates");
}

}  // namespace
