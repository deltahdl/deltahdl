#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(StdBuiltinPackage, UserPackageNamedStdIsRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package std;\n"
             "  typedef int t;\n"
             "endpackage\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'std' is reserved for the built-in package and "
                            "cannot be declared by the user",
                            1, "26.7"));
}

TEST(StdBuiltinPackage, EmptyUserPackageNamedStdIsRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("package std;\n"
             "endpackage\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'std' is reserved for the built-in package and "
                            "cannot be declared by the user",
                            1, "26.7"));
}

TEST(StdBuiltinPackage, ModuleWildcardImportOfStdElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  import std::*;\n"
             "endmodule\n"));
}

TEST(StdBuiltinPackage, StdScopeResolutionBaseIsAcceptedInElaboration) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int x;\n"
             "  int q;\n"
             "  initial q = std::randomize(x);\n"
             "endmodule\n"));
}

TEST(StdBuiltinPackage, UnknownScopeResolutionBaseIsRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  int x;\n"
             "  int q;\n"
             "  initial q = nope::randomize(x);\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved package or scope 'nope'",
                            4, "26.3"));
}

TEST(StdBuiltinPackage, StdIsImplicitlyWildcardImported) {
  ElabFixture f;
  auto* design = Elaborate("module m; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  bool has_std_wildcard = false;
  for (const auto& imp : mod->imports) {
    if (imp.package_name == "std" && imp.is_wildcard) has_std_wildcard = true;
  }
  EXPECT_TRUE(has_std_wildcard);
}

TEST(StdPackage, ScopedReferenceToANameStdDoesNotDeclareIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("module top;\n"
             "  int v;\n"
             "  initial begin\n"
             "    v = std::nosuch;\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to 'std::nosuch', which package 'std' "
                            "neither declares nor exports",
                            4, "26.3"));
}

TEST(StdPackage, ScopedReferenceToAStdClassElaborates) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  std::process p;\n"
             "  initial begin\n"
             "    p = std::process::self();\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
