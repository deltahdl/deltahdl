#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(ConfigPackageBinding, CellClauseSelectingPackageIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg; endpackage\n"
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  cell pkg use lib1.other;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "config 'c' cell clause selects package 'pkg'", 5,
                            "33.4"));
}

TEST(ConfigPackageBinding, UseClauseBindingInstanceToPackageIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg; endpackage\n"
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a use pkg;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "config 'c' use clause binds an instance to package 'pkg'", 5, "33.4"));
}

TEST(ConfigPackageBinding, UseClauseBindingInstanceToModuleIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module sub; endmodule\n"
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a use sub;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigPackageBinding, UnreferencedPackageDoesNotTripProhibition) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg; endpackage\n"
      "module sub; endmodule\n"
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a use sub;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigPackageBinding, CellClauseSelectingModuleIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module sub; endmodule\n"
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  cell sub use lib1.other;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigPackageBinding, CellClauseNamingModuleSharingAPackagesNameAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "package p; endpackage\n"
      "module p; endmodule\n"
      "module top; p u(); endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  cell p liblist work;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigPackageBinding,
     CellClauseSelectingModuleWithPackageDeclaredIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg; endpackage\n"
      "module sub; endmodule\n"
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  cell sub use lib1.other;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigPackageBinding, UseClauseBindingInstanceToInterfaceIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; endinterface\n"
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a use ifc;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigPackageBinding, UseClauseBindingInstanceToProgramIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "program prog; endprogram\n"
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a use prog;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ConfigPackageBinding, UseClauseBindingInstanceToPrimitiveIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "primitive prim(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a use prim;\n"
      "endconfig\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
