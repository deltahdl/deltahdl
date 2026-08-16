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
  // The `std` name is reserved for the built-in package regardless of what the
  // user package would contain: even an empty `package std` is illegal, since
  // users cannot supply declarations for the built-in package.
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
  // §26.7: `std ::` names the always-available built-in package, so a
  // `std ::`-qualified reference is never diagnosed as an unresolved package or
  // scope. Drive a std-scoped reference through elaboration -- its scope base
  // flows through the scope-resolution base check -- and observe that it
  // elaborates cleanly. Contrast with the unknown-base foil below, which is
  // identical except for the base identifier.
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int x;\n"
             "  int q;\n"
             "  initial q = std::randomize(x);\n"
             "endmodule\n"));
}

TEST(StdBuiltinPackage, UnknownScopeResolutionBaseIsRejected) {
  // Foil for the rule above: `std` is accepted only because it is the built-in
  // package. The same reference through a base that names no declared package
  // (and is not `std`) must be rejected -- confirming the acceptance of `std`
  // is specific to the built-in package, not a blanket pass for every
  // `base ::` prefix.
  // The rejection is reported under §26.3, not §26.7: the base is diagnosed by
  // ReportUnknownScopeBases in src/elaborator/elaborator_scope_rules.cpp.
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
  // §26.7: every module receives an implicit wildcard import of the built-in
  // `std` package, even when the source contains no import declaration. Observe
  // the import the elaborator injects on the elaborated module.
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

}  // namespace
