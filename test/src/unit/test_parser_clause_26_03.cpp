#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(PackageImport, PackageImportMultiple) {
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

TEST(PackageImport, ModuleImportPackage) {
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

TEST(PackageImport, ModuleImportSpecific) {
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
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kImportDecl);
  ASSERT_NE(imp, nullptr);
  EXPECT_EQ(imp->import_item.package_name, "p");
  EXPECT_EQ(imp->import_item.item_name, "X");
}

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

TEST(PackageImport, ModuleMultipleImports) {
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

TEST(PackageScopeReference, PackageScopeInExpression) {
  auto r = Parse("module m; initial x = pkg::my_const; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
}

TEST(PackageScopeReference, PackageScopedFunctionCall) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  function int f(); return 1; endfunction\n"
              "endpackage\n"
              "module m;\n"
              "  int x;\n"
              "  initial x = pkg::f();\n"
              "endmodule\n"));
}

TEST(PackageImport, ImportWildcardField) {
  auto r = Parse(
      "package p;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  const auto* imp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kImportDecl);
  ASSERT_NE(imp, nullptr);
  EXPECT_EQ(imp->import_item.package_name, "p");
  EXPECT_TRUE(imp->import_item.is_wildcard);
}

TEST_F(AnnexHParseTest, AnnexGStdRandomizePackageImport) {
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

TEST(PackageImport, MultiItemImport) {
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

TEST(PackageImport, MultiItemImportWithWildcardFirst) {
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

TEST(PackageImport, MultiItemImportWithWildcardSecond) {
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

TEST(PackageScopeReference, ScopeResolutionType) {
  auto r = Parse(
      "module t;\n"
      "  import pkg::mytype;\n"
      "  pkg::mytype x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);

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

TEST(PackageImport, PackageImportExplicit) {
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

TEST(PackageImport, PackageWildcardImport) {
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

TEST(PackageImport, MultiplePackageImports) {
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

TEST(PackageScopeReference, PackageScopeResolution) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  parameter int WIDTH = 8;\n"
              "endpackage\n"
              "module m;\n"
              "  logic [pkg::WIDTH-1:0] data;\n"
              "endmodule\n"));
}

TEST(PackageImport, PackageImportItemStar) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "module m; import pkg::*; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->import_item.package_name, "pkg");
  EXPECT_TRUE(item->import_item.is_wildcard);
}

TEST(PackageImport, ImportInTask) {
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

TEST(PackageImport, ImportMultipleInBlock) {
  EXPECT_TRUE(
      ParseOk("package p1; int a; endpackage\n"
              "package p2; int b; endpackage\n"
              "module m;\n"
              "  initial begin\n"
              "    import p1::a, p2::b;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(PackageImport, ImportSpecific) {
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

TEST(PackageImport, ImportWildcard) {
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

TEST_F(ProgramParseTest, ProgramWithImportStatement) {
  auto* unit = Parse(
      "program p;\n"
      "  import pkg::*;\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->programs[0]->name, "p");
  EXPECT_EQ(unit->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(unit->programs[0]->items[0]->import_item.package_name, "pkg");
  EXPECT_TRUE(unit->programs[0]->items[0]->import_item.is_wildcard);
}

TEST(PackageImport, WildcardIntoInterface) {
  EXPECT_TRUE(
      ParseOk("package pkg; typedef int myint; endpackage\n"
              "interface ifc;\n"
              "  import pkg::*;\n"
              "endinterface\n"));
}

TEST(PackageImport, WildcardIntoProgram) {
  EXPECT_TRUE(
      ParseOk("package pkg; typedef int myint; endpackage\n"
              "program p;\n"
              "  import pkg::*;\n"
              "endprogram\n"));
}

TEST(PackageImport, WildcardIntoPackage) {
  EXPECT_TRUE(
      ParseOk("package a; typedef int myint; endpackage\n"
              "package b;\n"
              "  import a::*;\n"
              "endpackage\n"));
}

TEST(PackageImport, PackagePrecedesImport) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "  byte_t data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kImportDecl));
}

}  // namespace
