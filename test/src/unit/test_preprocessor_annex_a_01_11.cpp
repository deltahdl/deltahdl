#include "fixture_parser.h"

using namespace delta;

namespace {

// --- Moved from test_preprocessor_clause_26_02.cpp ---

TEST(PackageItemsParsing, PackageItemTimeunitsDecl) {
  auto r = ParseWithPreprocessor(
      "package pkg;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, ConditionalPackageItem) {
  auto r = ParseWithPreprocessor(
      "`define INCLUDE_FUNC\n"
      "package pkg;\n"
      "`ifdef INCLUDE_FUNC\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "`endif\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_FALSE(r.cu->packages[0]->items.empty());
}

TEST(PackageItemsParsing, ConditionalPackageItemExcluded) {
  auto r = ParseWithPreprocessor(
      "package pkg;\n"
      "`ifdef NOT_DEFINED\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "`endif\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, MacroExpandedPackageItem) {
  auto r = ParseWithPreprocessor(
      "`define PKG_PARAM parameter int WIDTH = 8;\n"
      "package pkg;\n"
      "  `PKG_PARAM\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_FALSE(r.cu->packages[0]->items.empty());
}

}  // namespace
