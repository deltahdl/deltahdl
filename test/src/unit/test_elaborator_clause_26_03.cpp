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

TEST(WildcardImport, MultiplePackages) {
  EXPECT_TRUE(
      ElabOk("package p1;\n"
             "  typedef int t1;\n"
             "endpackage\n"
             "package p2;\n"
             "  typedef int t2;\n"
             "endpackage\n"
             "module m;\n"
             "  import p1::*;\n"
             "  import p2::*;\n"
             "endmodule\n"));
}

}  // namespace
