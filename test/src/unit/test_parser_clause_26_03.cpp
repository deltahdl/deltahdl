// §26.3: Referencing data in packages

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA213, DataDeclPackageImport) {
  // package_import_declaration alternative
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; import pkg::*; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA213, PackageImportMultiple) {
  // Multiple comma-separated import items
  auto r = Parse(
      "package p1; endpackage\n"
      "package p2; endpackage\n"
      "module m; import p1::a, p2::b; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int import_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kImportDecl) import_count++;
  }
  EXPECT_GE(import_count, 2);
}

// --- package_import_declaration ---
// import package_import_item { , package_import_item } ;
TEST(ParserA213, PackageImportSingle) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; import pkg::foo; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(item->import_item.package_name, "pkg");
  EXPECT_EQ(item->import_item.item_name, "foo");
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

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

struct ParseResult40 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult40 Parse(const std::string& src) {
  ParseResult40 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// =============================================================================
// Coexistence with package imports/exports
// =============================================================================
TEST_F(DpiParseTest, PackageImportStillWorks) {
  auto* unit = Parse(R"(
    module m;
      import pkg::*;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kImportDecl);
}

// =============================================================================
// LRM section 26.3 -- Multiple imports and wildcard
// =============================================================================
TEST(ParserSection26, ModuleMultipleImports) {
  auto r = Parse(
      "package p1;\n"
      "endpackage\n"
      "package p2;\n"
      "endpackage\n"
      "module m;\n"
      "  import p1::*;\n"
      "  import p2::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  size_t import_count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kImportDecl) ++import_count;
  }
  EXPECT_EQ(import_count, 2u);
}

// =============================================================================
// A.8.4 Primaries — class_qualifier
// =============================================================================
// § class_qualifier — class_scope
TEST(ParserA84, ClassQualifierScope) {
  auto r = Parse("module m; initial x = pkg::my_const; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
}

TEST(ParserSection26, ImportWildcardField) {
  auto r = Parse(
      "package p;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  const auto* imp =
      FindItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kImportDecl);
  ASSERT_NE(imp, nullptr);
  EXPECT_EQ(imp->import_item.package_name, "p");
  EXPECT_TRUE(imp->import_item.is_wildcard);
}

TEST_F(AnnexHParseTest, AnnexGStdRandomizePackageImport) {
  // std::randomize usage via package import at module level.
  // The parser handles import std_pkg::* for scope-qualified access.
  auto* unit = Parse(
      "module m;\n"
      "  import std_pkg::*;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = $urandom_range(0, 255);\n"
      "    b = $urandom;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
  auto& items = unit->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kImportDecl);
}

TEST(ParserSection26, ImportSpecificNotWildcard) {
  auto r = Parse(
      "package p;\n"
      "  parameter int X = 1;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::X;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  const auto* imp =
      FindItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kImportDecl);
  ASSERT_NE(imp, nullptr);
  EXPECT_FALSE(imp->import_item.is_wildcard);
  EXPECT_EQ(imp->import_item.item_name, "X");
}

}  // namespace
