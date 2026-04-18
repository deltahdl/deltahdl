#include "fixture_elaborator.h"

namespace {

TEST(StdBuiltinPackage, UserPackageNamedStdIsRejected) {
  // §26.7 reserves std for the built-in package, so a user-declared
  // package named std must be rejected regardless of its contents.
  EXPECT_FALSE(
      ElabOk("package std;\n"
             "  typedef int t;\n"
             "endpackage\n"
             "module m; endmodule\n"));
}

TEST(StdBuiltinPackage, ModuleWildcardImportOfStdElaborates) {
  // std is a known package identifier; an explicit wildcard import is legal
  // and elaborates cleanly alongside the implicit CU-scope import.
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  import std::*;\n"
             "endmodule\n"));
}

TEST(StdBuiltinPackage, StdIsImplicitlyWildcardImported) {
  // A module that neither declares nor imports std should still elaborate
  // successfully; the implicit CU-scope import must not raise diagnostics.
  EXPECT_TRUE(ElabOk("module m; endmodule\n"));
}

}  // namespace
