#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TypeDeclParsing, PackageExportMultipleItems) {
  auto r = Parse(
      "package pkg;\n"
      "  export p1::a, p2::b;\n"
      "endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int export_count = 0;
  for (auto* item : r.cu->packages[0]->items) {
    if (item->kind == ModuleItemKind::kExportDecl) export_count++;
  }
  EXPECT_GE(export_count, 2);
}

TEST(PackageParsing, PackageExportWildcard) {
  auto r = Parse(
      "package p;\n"
      "  export *::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kExportDecl));
}

TEST(PackageParsing, PackageExportSpecific) {
  auto r = Parse(
      "package p;\n"
      "  export other_pkg::some_func;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(ModuleAndHierarchyParsing, ExportDecl) {
  auto r = Parse(
      "package p;\n"
      "  export pkg::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  auto* pkg = r.cu->packages[0];
  ASSERT_EQ(pkg->items.size(), 1);
  EXPECT_EQ(pkg->items[0]->kind, ModuleItemKind::kExportDecl);
  EXPECT_EQ(pkg->items[0]->import_item.package_name, "pkg");
  EXPECT_TRUE(pkg->items[0]->import_item.is_wildcard);
}

TEST(ModuleAndHierarchyParsing, ExportWildcardAll) {
  auto r = Parse(
      "package p;\n"
      "  export *::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  auto* pkg = r.cu->packages[0];
  ASSERT_EQ(pkg->items.size(), 1);
  EXPECT_EQ(pkg->items[0]->kind, ModuleItemKind::kExportDecl);
  EXPECT_EQ(pkg->items[0]->import_item.package_name, "*");
  EXPECT_TRUE(pkg->items[0]->import_item.is_wildcard);
}

TEST(SourceText, PackageExportNamed) {
  auto r = Parse(
      "package pkg;\n"
      "  export other_pkg::my_func;\n"
      "  export another::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_GE(r.cu->packages[0]->items.size(), 2u);
}

TEST(TypeDeclParsing, PackageExportSingleItem) {
  auto r = Parse(
      "package pkg;\n"
      "  export other_pkg::some_func;\n"
      "endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->packages[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kExportDecl);
  EXPECT_EQ(item->import_item.package_name, "other_pkg");
  EXPECT_EQ(item->import_item.item_name, "some_func");
}

}  // namespace
