#include "fixture_elaborator.h"

namespace {

TEST(StdBuiltinPackage, UserPackageNamedStdIsRejected) {

  EXPECT_FALSE(
      ElabOk("package std;\n"
             "  typedef int t;\n"
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

  EXPECT_TRUE(ElabOk("module m; endmodule\n"));
}

}
