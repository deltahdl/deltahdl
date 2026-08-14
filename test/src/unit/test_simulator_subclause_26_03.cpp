#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(PackageImportSim, WildcardImportParameter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  parameter int VAL = 99;\n"
      "endpackage\n"
      "module t;\n"
      "  import pkg::*;\n"
      "  logic [7:0] x;\n"
      "  initial x = VAL;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 99u);
}

TEST(PackageScopeReferenceSim, PackageScopeParamResolves) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  parameter int WIDTH = 16;\n"
      "endpackage\n"
      "module t;\n"
      "  logic [31:0] y;\n"
      "  initial y = pkg::WIDTH;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 16u);
}

// §26.3: a wildcard import brings a package's enumeration literals into the
// importing scope. Drive one through the full pipeline and observe that the
// unqualified literal reference evaluates to its ordinal value at run time.
TEST(PackageImportSim, WildcardImportEnumLiteralEvaluates) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  typedef enum { LOW, MID, HIGH } level_t;\n"
      "endpackage\n"
      "module t;\n"
      "  import pkg::*;\n"
      "  level_t sel;\n"
      "  logic [31:0] y;\n"
      "  initial begin\n"
      "    sel = HIGH;\n"
      "    y = sel;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 2u);
}

TEST(PackageImportSim, ExplicitImportParameter) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  parameter int VAL = 77;\n"
      "endpackage\n"
      "module t;\n"
      "  import pkg::VAL;\n"
      "  logic [31:0] y;\n"
      "  initial y = VAL;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 77u);
}

// §26.3: the package scope resolution operator resolves a package localparam at
// run time, just as it does a parameter. A localparam takes a different
// constant form (§11.2.1) than a parameter, so observe its value end to end.
TEST(PackageScopeReferenceSim, PackageScopeLocalparamResolves) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  localparam int W = 24;\n"
      "endpackage\n"
      "module t;\n"
      "  logic [31:0] y;\n"
      "  initial y = pkg::W;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 24u);
}

// §26.3: an explicit import brings a package function into the importing scope
// so it can be called with an unqualified name. Drive the imported call through
// the full pipeline and observe its returned value at run time.
TEST(PackageImportSim, ExplicitImportFunctionCalledUnqualified) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  function automatic int scale(int a);\n"
      "    return a * 5;\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  import pkg::scale;\n"
      "  logic [31:0] y;\n"
      "  initial y = scale(4);\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 20u);
}

// §26.3: a package import makes the package's names visible unqualified in the
// scope that writes the import, and this case holds that the scope may be a
// module reached through an instance. §26.3 (printed page 809 of ~/LRM.pdf)
// states the visibility the read rests on: the import declaration "allows
// identifiers declared within packages to be visible within the current scope
// without a package name qualifier".
//
// The case is a guard rail rather than a defect-catcher. It passes today, and
// it must keep passing after the fix for #3054 narrows SimContext::FindVariable
// so a bare name referenced inside an instance no longer falls back to the
// unprefixed key. AliasPackageDataItem (src/simulator/lowerer_import.cpp) binds
// an imported name under exactly that unprefixed key, so the narrowing reaches
// this read unless it exempts an imported name. Every other import case in this
// file imports into the top module, where no instance prefix is in force, so
// none of them constrains the narrowing.
//
// `top` imports pkg::VAL as well as `child` because the top's import is what
// binds the name today: Lowerer::LowerImports runs for the top module only, and
// Lowerer::LowerChildModules (src/simulator/lowerer_child.cpp) never calls it,
// so the child's own import is lowered nowhere.
TEST(PackageImportSim, InstantiatedModuleReadsImportedParameter) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "package pkg;\n"
      "  parameter int VAL = 77;\n"
      "endpackage\n"
      "module child;\n"
      "  import pkg::VAL;\n"
      "  logic [31:0] y;\n"
      "  initial y = VAL;\n"
      "endmodule\n"
      "module top;\n"
      "  import pkg::VAL;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "u1.y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 77u);
}

}  // namespace
