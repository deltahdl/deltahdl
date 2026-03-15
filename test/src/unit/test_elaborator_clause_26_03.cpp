// §26.3

#include "fixture_elaborator.h"

namespace {

TEST(PackageWildcardImport, ModuleWithPackageElaborates) {
  EXPECT_TRUE(
      ElabOk("package pkg;\n"
             "  typedef int myint;\n"
             "endpackage\n"
             "module m;\n"
             "  import pkg::*;\n"
             "endmodule\n"));
}

}  // namespace
