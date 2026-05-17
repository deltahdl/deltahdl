#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

}
