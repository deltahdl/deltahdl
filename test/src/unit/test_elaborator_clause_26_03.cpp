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

TEST(WildcardPackageImport, ModuleWithPackageImportAndUsage) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "  byte_t x;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
