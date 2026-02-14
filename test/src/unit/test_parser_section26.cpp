#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// =============================================================================
// LRM section 26.2 -- Package declarations
// =============================================================================

TEST(ParserSection26, EmptyPackage) {
  auto r = Parse(
      "package pkg;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

TEST(ParserSection26, PackageWithEndLabel) {
  auto r = Parse(
      "package my_pkg;\n"
      "endpackage : my_pkg\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "my_pkg");
}

TEST(ParserSection26, PackageWithTypedef) {
  auto r = Parse(
      "package types_pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  ASSERT_FALSE(r.cu->packages[0]->items.empty());
  EXPECT_EQ(r.cu->packages[0]->items[0]->kind, ModuleItemKind::kTypedef);
}

TEST(ParserSection26, PackageWithParameter) {
  auto r = Parse(
      "package cfg_pkg;\n"
      "  parameter int WIDTH = 8;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  ASSERT_FALSE(r.cu->packages[0]->items.empty());
}

static bool HasItemOfKind(const std::vector<ModuleItem*>& items,
                          ModuleItemKind kind) {
  for (const auto* item : items) {
    if (item->kind == kind) return true;
  }
  return false;
}

TEST(ParserSection26, PackageWithFunction) {
  auto r = Parse(
      "package util_pkg;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kFunctionDecl));
}

// =============================================================================
// LRM section 26.3 -- Referencing data in packages (import)
// =============================================================================

TEST(ParserSection26, ModuleImportPackage) {
  auto r = Parse(
      "package p;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kImportDecl));
}

static const ModuleItem* FindItemOfKind(const std::vector<ModuleItem*>& items,
                                        ModuleItemKind kind) {
  for (const auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

TEST(ParserSection26, ModuleImportSpecific) {
  auto r = Parse(
      "package p;\n"
      "  parameter int X = 1;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::X;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  const auto* imp =
      FindItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kImportDecl);
  ASSERT_NE(imp, nullptr);
  EXPECT_EQ(imp->import_item.package_name, "p");
  EXPECT_EQ(imp->import_item.item_name, "X");
}

// =============================================================================
// LRM section 26.6 -- Exporting from packages
// =============================================================================

TEST(ParserSection26, PackageExportWildcard) {
  auto r = Parse(
      "package p;\n"
      "  export *::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kExportDecl));
}

TEST(ParserSection26, PackageExportSpecific) {
  auto r = Parse(
      "package p;\n"
      "  export other_pkg::some_func;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(ParserSection26, MultiplePackages) {
  auto r = Parse(
      "package a;\n"
      "endpackage\n"
      "package b;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 2u);
  EXPECT_EQ(r.cu->packages[0]->name, "a");
  EXPECT_EQ(r.cu->packages[1]->name, "b");
}
