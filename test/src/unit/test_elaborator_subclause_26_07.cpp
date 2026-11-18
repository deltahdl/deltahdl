#include <gtest/gtest.h>

#include <string>

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

void ExpectStdReferenceRefused(const std::string& src, const std::string& name,
                               int line) {
  SCOPED_TRACE(src);
  ElabFixture f;
  EXPECT_FALSE(ElabOk(src, f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to '" + name +
                                "', which package 'std' neither declares nor "
                                "exports",
                            line, "26.3"));
}

TEST(StdPackage, AScopedCallOfAFunctionStdDoesNotDeclareIsReported) {
  ExpectStdReferenceRefused(
      "module top; int x, r;\n"
      "initial r = std::nosuchfn(x);\n"
      "endmodule\n",
      "std::nosuchfn", 2);
  ExpectStdReferenceRefused(
      "module top; function int f(); return 3; endfunction int r;\n"
      "initial r = std::f();\n"
      "endmodule\n",
      "std::f", 2);
  ElabFixture f;
  EXPECT_TRUE(ElabOk(
      "module top; int x, r; initial r = std::randomize(x); endmodule\n", f));
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(StdPackage, DISABLED_AScopedTaskCallOrTypeStdDoesNotDeclareIsReported) {
  ExpectStdReferenceRefused(
      "module top;\n"
      "initial std::sys_task();\n"
      "endmodule\n",
      "std::sys_task", 2);
  ExpectStdReferenceRefused(
      "module top;\n"
      "std::nosuchtype v;\n"
      "endmodule\n",
      "std::nosuchtype", 2);
}

TEST(StdPackage, ACompilationUnitDeclarationDoesNotJoinStd) {
  ExpectStdReferenceRefused(
      "int foo;\n"
      "module top; int r;\n"
      "initial r = std::foo;\n"
      "endmodule\n",
      "std::foo", 3);
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("int foo;\nmodule top; int r; initial r = foo; endmodule\n", f));
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
