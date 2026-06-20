#include "fixture_elaborator.h"

namespace {

// §33.4: a configuration may change the binding of a module, primitive,
// interface, or program instance, but shall not change the binding of a
// package. A cell clause that selects a package as the cell being
// reconfigured therefore must be rejected.
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
  EXPECT_TRUE(f.has_errors);
}

// A use clause that binds a selected instance to a package likewise changes
// the binding of a package and must be rejected (§33.4).
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
  EXPECT_TRUE(f.has_errors);
}

// The companion positive case: a configuration may change the binding of a
// module instance, so a use clause naming an ordinary module is accepted.
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

// A package coexisting with configs that never reference it must not trip the
// prohibition: the rule applies only when a clause actually names the package.
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

// A library qualifier on the use clause target must not let a package binding
// slip past the prohibition: a configuration cannot redirect to a package even
// when the package is named with an explicit library (§33.4).
TEST(ConfigPackageBinding, LibraryQualifiedUseClauseToPackageIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "package pkg; endpackage\n"
      "module top; endmodule\n"
      "config c;\n"
      "  design top;\n"
      "  instance top.a use lib1.pkg;\n"
      "endconfig\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// The cell-clause path must not over-fire: selecting an ordinary module (not a
// package) for reconfiguration is exactly what §33.4 permits, so it is
// accepted.
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

}  // namespace
