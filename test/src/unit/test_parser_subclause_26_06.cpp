#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

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

TEST(PackageExportParsing, ExportInAModuleBodyIsReported) {
  auto r = Parse(
      "package p1; int x = 5; endpackage\n"
      "module top;\n"
      "  import p1::*;\n"
      "  export p1::x;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a package export declaration is allowed only in a package", 4,
      "26.6"));
}

TEST(PackageExportParsing, DpiExportInAModuleBodyStaysLegal) {
  auto r = Parse(
      "module top;\n"
      "  export \"DPI-C\" function f;\n"
      "  function void f(); endfunction\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageExportParsing, ExportStarStarTakesNoList) {
  auto r = Parse(
      "package p1; int x = 5; endpackage\n"
      "package p2;\n"
      "  import p1::x;\n"
      "  export *::*, p1::x;\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got ','", 4, "26.6"));
}

}  // namespace
