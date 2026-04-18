#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(PackageExportParsing, ExportStarStar) {
  auto r = Parse(
      "package p;\n"
      "  export *::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  auto* pkg = r.cu->packages[0];
  ASSERT_EQ(pkg->items.size(), 1u);
  EXPECT_EQ(pkg->items[0]->kind, ModuleItemKind::kExportDecl);
  EXPECT_EQ(pkg->items[0]->import_item.package_name, "*");
  EXPECT_TRUE(pkg->items[0]->import_item.is_wildcard);
}

TEST(PackageExportParsing, ExportPackageWildcard) {
  auto r = Parse(
      "package p;\n"
      "  export pkg::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* pkg = r.cu->packages[0];
  ASSERT_EQ(pkg->items.size(), 1u);
  EXPECT_EQ(pkg->items[0]->kind, ModuleItemKind::kExportDecl);
  EXPECT_EQ(pkg->items[0]->import_item.package_name, "pkg");
  EXPECT_TRUE(pkg->items[0]->import_item.is_wildcard);
}

TEST(PackageExportParsing, ExportSpecificItem) {
  auto r = Parse(
      "package p;\n"
      "  export other_pkg::some_func;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* pkg = r.cu->packages[0];
  ASSERT_EQ(pkg->items.size(), 1u);
  auto* item = pkg->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kExportDecl);
  EXPECT_EQ(item->import_item.package_name, "other_pkg");
  EXPECT_EQ(item->import_item.item_name, "some_func");
  EXPECT_FALSE(item->import_item.is_wildcard);
}

TEST(PackageExportParsing, ExportMultipleItemsInOneDecl) {
  // A.2.1.3: `export package_import_item { , package_import_item } ;` — the
  // parser splits each import_item into its own ModuleItem entry.
  auto r = Parse(
      "package p;\n"
      "  export p1::a, p2::b;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* pkg = r.cu->packages[0];
  int export_count = 0;
  for (auto* item : pkg->items) {
    if (item->kind == ModuleItemKind::kExportDecl) ++export_count;
  }
  EXPECT_EQ(export_count, 2);
}

TEST(PackageExportParsing, ExportFollowingMatchingImport) {
  auto r = Parse(
      "package p;\n"
      "  import other_pkg::foo;\n"
      "  export other_pkg::foo;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kExportDecl));
}

TEST(PackageExportParsing, ExportPrecedingMatchingImport) {
  // §26.6 allows a package export to appear before its matching import.
  auto r = Parse(
      "package p;\n"
      "  export other_pkg::foo;\n"
      "  import other_pkg::foo;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageExportParsing, ExportMixOfSpecificAndWildcard) {
  auto r = Parse(
      "package pkg;\n"
      "  export other_pkg::my_func;\n"
      "  export another::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int export_count = 0;
  for (auto* item : r.cu->packages[0]->items) {
    if (item->kind == ModuleItemKind::kExportDecl) ++export_count;
  }
  EXPECT_EQ(export_count, 2);
}

TEST(PackageExportParsing, PackageContainingOnlyExports) {
  auto r = Parse(
      "package pkg;\n"
      "  export other_pkg::item1;\n"
      "  export *::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->items.size(), 2u);
}

}  // namespace
