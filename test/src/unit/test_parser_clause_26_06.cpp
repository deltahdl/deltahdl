#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

TEST(PackageExportParsing, ExportListWithCommaSeparatedItems) {
  // BNF alternative: export package_import_item { , package_import_item } ;
  // A single export declaration may carry a comma-separated list, and the
  // parser emits one export item per element of that list.
  auto r = Parse(
      "package pkg;\n"
      "  export other_pkg::a, other_pkg::b, other_pkg::c;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  int export_count = 0;
  for (auto* item : r.cu->packages[0]->items) {
    if (item->kind == ModuleItemKind::kExportDecl) ++export_count;
  }
  EXPECT_EQ(export_count, 3);
}

TEST(PackageExportParsing, ExportListMixesSpecificAndWildcardItems) {
  // Each package_import_item in the comma list may independently be a specific
  // name (pkg::name) or a wildcard (pkg::*); the parser accepts a mix and
  // flags the wildcard element accordingly.
  auto r = Parse(
      "package pkg;\n"
      "  export p1::a, p2::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  int specific_count = 0;
  int wildcard_count = 0;
  for (auto* item : r.cu->packages[0]->items) {
    if (item->kind != ModuleItemKind::kExportDecl) continue;
    if (item->import_item.is_wildcard) {
      ++wildcard_count;
    } else {
      ++specific_count;
    }
  }
  EXPECT_EQ(specific_count, 1);
  EXPECT_EQ(wildcard_count, 1);
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

}
