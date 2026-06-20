#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(StdBuiltinPackage, UserPackageNamedStdIsRejected) {
  EXPECT_FALSE(
      ElabOk("package std;\n"
             "  typedef int t;\n"
             "endpackage\n"
             "module m; endmodule\n"));
}

TEST(StdBuiltinPackage, EmptyUserPackageNamedStdIsRejected) {
  // The `std` name is reserved for the built-in package regardless of what the
  // user package would contain: even an empty `package std` is illegal, since
  // users cannot supply declarations for the built-in package.
  EXPECT_FALSE(
      ElabOk("package std;\n"
             "endpackage\n"
             "module m; endmodule\n"));
}

TEST(StdBuiltinPackage, ModuleWildcardImportOfStdElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  import std::*;\n"
             "endmodule\n"));
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
