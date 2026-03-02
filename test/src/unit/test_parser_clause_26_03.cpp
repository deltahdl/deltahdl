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

struct ParseResult23b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult23b Parse(const std::string& src) {
  ParseResult23b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

TEST(ParserSection23, MultiItemImport) {
  auto r = Parse(
      "module m;\n"
      "  import pkg::a, pkg::b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  VerifyImportItem(mod->items[0], "pkg", "a");
  VerifyImportItem(mod->items[1], "pkg", "b");
}

TEST(ParserSection23, MultiItemImportWithWildcardFirst) {
  auto r = Parse(
      "module m;\n"
      "  import pkg::*, other::func;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  EXPECT_EQ(mod->items[0]->import_item.package_name, "pkg");
  EXPECT_TRUE(mod->items[0]->import_item.is_wildcard);
}

TEST(ParserSection23, MultiItemImportWithWildcardSecond) {
  auto r = Parse(
      "module m;\n"
      "  import pkg::*, other::func;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  EXPECT_EQ(mod->items[1]->import_item.package_name, "other");
  EXPECT_EQ(mod->items[1]->import_item.item_name, "func");
}

struct ParseResult6b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult6b Parse(const std::string& src) {
  ParseResult6b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// =========================================================================
// §6.25: Parameterized data types
// =========================================================================
TEST(ParserSection6, ScopeResolutionType) {
  auto r = Parse(
      "module t;\n"
      "  import pkg::mytype;\n"
      "  pkg::mytype x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // Find the variable declaration.
  auto& items = r.cu->modules[0]->items;
  ModuleItem* var_item = nullptr;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kVarDecl && it->name == "x") {
      var_item = it;
      break;
    }
  }
  ASSERT_NE(var_item, nullptr);
  EXPECT_EQ(var_item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(var_item->data_type.scope_name, "pkg");
  EXPECT_EQ(var_item->data_type.type_name, "mytype");
}

// 9. Package import with :: operator
TEST(ParserClause03, Cl3_13_PackageImportExplicit) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int myint;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::myint;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  auto* item = mod->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(item->import_item.package_name, "pkg");
  EXPECT_EQ(item->import_item.item_name, "myint");
  EXPECT_FALSE(item->import_item.is_wildcard);
}

// 10. Package wildcard import (import pkg::*)
TEST(ParserClause03, Cl3_13_PackageWildcardImport) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int myint;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  auto* item = mod->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(item->import_item.package_name, "pkg");
  EXPECT_TRUE(item->import_item.is_wildcard);
}

// 11. Multiple packages imported into same module
TEST(ParserClause03, Cl3_13_MultiplePackageImports) {
  auto r = Parse(
      "package alpha;\n"
      "  typedef int alpha_t;\n"
      "endpackage\n"
      "package beta;\n"
      "  typedef int beta_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import alpha::*;\n"
      "  import beta::beta_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 2u);
  auto* mod = r.cu->modules[0];
  int import_count = 0;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kImportDecl) import_count++;
  }
  EXPECT_EQ(import_count, 2);
}

// 20. Package scope resolution (pkg::item)
TEST(ParserClause03, Cl3_13_PackageScopeResolution) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  parameter int WIDTH = 8;\n"
              "endpackage\n"
              "module m;\n"
              "  logic [pkg::WIDTH-1:0] data;\n"
              "endmodule\n"));
}

TEST(ParserA213, PackageImportItemStar) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; import pkg::*; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->import_item.package_name, "pkg");
  EXPECT_TRUE(item->import_item.is_wildcard);
}

// import in task body
TEST(ParserA28, ImportInTask) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  int val = 1;\n"
              "endpackage\n"
              "module m;\n"
              "  task my_task();\n"
              "    import pkg::*;\n"
              "  endtask\n"
              "endmodule\n"));
}

// Multiple imports in one statement in block
TEST(ParserA28, ImportMultipleInBlock) {
  EXPECT_TRUE(
      ParseOk("package p1; int a; endpackage\n"
              "package p2; int b; endpackage\n"
              "module m;\n"
              "  initial begin\n"
              "    import p1::a, p2::b;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(Parser, ImportSpecific) {
  auto r = Parse(
      "module t;\n"
      "  import my_pkg::WIDTH;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(item->import_item.package_name, "my_pkg");
  EXPECT_EQ(item->import_item.item_name, "WIDTH");
  EXPECT_FALSE(item->import_item.is_wildcard);
}

TEST(Parser, ImportWildcard) {
  auto r = Parse(
      "module t;\n"
      "  import my_pkg::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(item->import_item.package_name, "my_pkg");
  EXPECT_TRUE(item->import_item.is_wildcard);
}

// =============================================================================
// §24.13 Program with import
// =============================================================================
TEST_F(ProgramTestParse, ProgramWithImport) {
  auto* unit = Parse(
      "program p;\n"
      "  import pkg::*;\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kImportDecl);
  EXPECT_TRUE(unit->programs[0]->items[0]->import_item.is_wildcard);
}

}  // namespace
