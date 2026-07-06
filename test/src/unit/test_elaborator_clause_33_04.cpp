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

// The cell-clause companion to the unreferenced-package guard above: with a
// package actually present in the design, a cell clause selecting an ordinary
// module must still be accepted. This exercises the prohibition's cell-clause
// discrimination against a live set of package names — the non-firing path when
// the selected cell is not a package — rather than the trivial case where no
// package exists at all (§33.4).
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

// §33.4 admits four element kinds on the accept side of the rule — module,
// primitive, interface, and program instances — and only excludes packages.
// The module case is covered above; the remaining three admitted kinds must
// also pass the prohibition when named by a use clause. Each target below is
// declared with that kind's own real syntax so the accepted input is built,
// not stubbed, and the prohibition is observed discriminating package from the
// full set of instantiable design elements rather than from module alone.

// A configuration may change the binding of an interface instance, so a use
// clause naming an interface is accepted (§33.4).
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

// A configuration may change the binding of a program instance, so a use clause
// naming a program is accepted (§33.4).
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

// A configuration may change the binding of a primitive instance, so a use
// clause naming a user-defined primitive is accepted (§33.4).
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
