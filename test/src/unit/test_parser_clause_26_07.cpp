#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(StdBuiltinPackageParsing, ModuleWildcardImportOfStd) {
  auto r = Parse(
      "module m;\n"
      "  import std::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  const auto* imp =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kImportDecl);
  ASSERT_NE(imp, nullptr);
  EXPECT_EQ(imp->import_item.package_name, "std");
  EXPECT_TRUE(imp->import_item.is_wildcard);
}

TEST(StdBuiltinPackageParsing, StdScopeResolutionCallWithArgument) {

  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    std::randomize(x);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(StdBuiltinPackageParsing, StdScopedDataTypeInVariableDeclaration) {

  auto r = Parse(
      "module m;\n"
      "  std::mailbox mb;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(StdBuiltinPackageParsing, UserPackageNamedStdParses) {

  auto r = Parse(
      "package std;\n"
      "  typedef int t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "std");
}

}
