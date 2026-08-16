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
// `top` imports pkg::VAL as well as `child` on purpose. This case holds the
// design in which both scopes import the same name, so neither the top's
// binding nor the child's own may be dropped and still leave this read at 77.
// The four cases below hold the designs in which the child imports alone.
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

// §26.3: the import declaration "allows identifiers declared within packages to
// be visible within the current scope without a package name qualifier"
// (printed page 809 of ~/LRM.pdf). The current scope here is `child`, and `top`
// imports nothing, so the child's own import is the only thing that can make
// VAL visible to `initial y = VAL;`.
//
// This catches an import written inside an instantiated module binding nothing.
// Lowerer::LowerImports runs for the top module only until #3056 is fixed, so
// today the read of VAL finds no variable and `u1.y` holds 0 rather than 77.
TEST(PackageImportSim, ChildAloneImportsParameterAndReadsItUnqualified) {
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
      "  child u1();\n"
      "endmodule\n",
      f, "u1.y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 77u);
}

// §26.3: a wildcard import makes every identifier of the package visible
// unqualified in the scope that writes it, and that scope is `child` here. The
// top imports nothing, so `initial y = VAL;` reads 77 only if the child's own
// wildcard import was lowered.
//
// The wildcard needs its own case because Lowerer::LowerImports takes a
// different arm for it than for a named import
// (src/simulator/lowerer_import.cpp): `imp.is_wildcard` selects
// LowerAllImported plus AliasAllPackageDataItems, where a named import selects
// LowerImportedName plus AliasNamedPackageDataItem. A fix for #3056 that runs
// only one of the two arms for a child instance leaves the other binding
// nothing, and no named-import case can see that.
TEST(PackageImportSim,
     ChildAloneWildcardImportsParameterAndReadsItUnqualified) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "package pkg;\n"
      "  parameter int VAL = 77;\n"
      "endpackage\n"
      "module child;\n"
      "  import pkg::*;\n"
      "  logic [31:0] y;\n"
      "  initial y = VAL;\n"
      "endmodule\n"
      "module top;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "u1.y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 77u);
}

// §26.3: the identifiers an import makes visible unqualified include a package
// subroutine, not only a package parameter, so an import written in `child`
// must let `initial y = scale(10);` call pkg::scale by its bare name. The top
// imports nothing.
//
// This catches a fix for #3056 that binds an imported parameter for a child
// instance and leaves an imported function bound nowhere. The two travel
// separate routes in src/simulator/lowerer_import.cpp: a function goes through
// LowerImportedName, while AliasPackageDataItem returns early for anything that
// is neither ModuleItemKind::kParamDecl nor ModuleItemKind::kVarDecl.
TEST(PackageImportSim, ChildAloneImportsFunctionAndCallsItUnqualified) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "package pkg;\n"
      "  function int scale(int x);\n"
      "    return x * 2;\n"
      "  endfunction\n"
      "endpackage\n"
      "module child;\n"
      "  import pkg::scale;\n"
      "  logic [31:0] y;\n"
      "  initial y = scale(10);\n"
      "endmodule\n"
      "module top;\n"
      "  child u1();\n"
      "endmodule\n",
      f, "u1.y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 20u);
}

// §26.3: an import makes a name visible within the current scope, and each
// instantiated module is its own scope. `childa` imports pkga::VAL and `childb`
// imports pkgb::VAL, both spelled VAL, so the value each instance reads is
// decided by which module wrote the import and not by which import ran first.
//
// This catches a fix for #3056 that binds the imported name under a flat
// unprefixed key. AliasPackageDataItem (src/simulator/lowerer_import.cpp) binds
// VAL under its bare spelling and returns early when ctx.FindVariable already
// holds that name, so under a flat key the instance lowered first wins and
// `u2.y` reads 11 instead of 22. A design with one instance, or with two
// instances importing the same package, cannot tell a flat key from a
// per-instance one.
TEST(PackageImportSim,
     TwoInstancesImportLikeNamedParametersFromDifferentPackages) {
  SimFixture f;
  auto* ya = RunAndFindVar(
      "package pkga;\n"
      "  parameter int VAL = 11;\n"
      "endpackage\n"
      "package pkgb;\n"
      "  parameter int VAL = 22;\n"
      "endpackage\n"
      "module childa;\n"
      "  import pkga::VAL;\n"
      "  logic [31:0] y;\n"
      "  initial y = VAL;\n"
      "endmodule\n"
      "module childb;\n"
      "  import pkgb::VAL;\n"
      "  logic [31:0] y;\n"
      "  initial y = VAL;\n"
      "endmodule\n"
      "module top;\n"
      "  childa u1();\n"
      "  childb u2();\n"
      "endmodule\n",
      f, "u1.y");
  ASSERT_NE(ya, nullptr);
  EXPECT_EQ(ya->value.ToUint64(), 11u);
  auto* yb = f.ctx.FindVariable("u2.y");
  ASSERT_NE(yb, nullptr);
  EXPECT_EQ(yb->value.ToUint64(), 22u);
}

}  // namespace
