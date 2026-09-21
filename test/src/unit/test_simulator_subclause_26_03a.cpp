#include <gtest/gtest.h>

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
// module reached through an instance. §26.3 (printed page 809 of ~/IEEE
// 1800-2023.pdf) states the visibility the read rests on: the import
// declaration "allows identifiers declared within packages to be visible within
// the current scope without a package name qualifier".
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
// (printed page 809 of ~/IEEE 1800-2023.pdf). The current scope here is
// `child`, and `top` imports nothing, so the child's own import is the only
// thing that can make VAL visible to `initial y = VAL;`.
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

// §26.3 (printed page 808 of ~/IEEE 1800-2023.pdf) references a package's
// declarations through the package name whether or not the package was
// imported, and §6.18 (printed page 118) makes an object declared with a
// typedef's name an object of the type the name stands for. A `pkg::nib_t v;`
// written as a block item of a sequential block is sized at run time from the
// design's type_widths table, which the elaborator keys by "pkg::nib_t" and
// which the simulator looked up by "nib_t" alone, so v was created at the
// 32-bit carrier that stands in for a type nothing could size: v = -1 read
// 4294967295 and $bits(v)
// 32. The -1 is the discriminating value, since 15 and 4294967295 differ.
TEST(PackageScopeReferenceSim, PackageScopedTypedefSizesBlockLocal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  typedef logic [3:0] nib_t;\n"
      "endpackage\n"
      "module t;\n"
      "  logic [31:0] w, b;\n"
      "  initial begin\n"
      "    pkg::nib_t v;\n"
      "    v = -1;\n"
      "    w = v;\n"
      "    b = $bits(v);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("w")->value.ToUint64(), 15u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 4u);
}

// The same lookup answers whether the name stands for a signed type (§6.11.1),
// which is what a relational operator reads. A block local declared with a
// package typedef of `byte` and set to -1 is below zero only when the simulator
// found the typedef behind its scoped name; created unsigned it reads 255.
TEST(PackageScopeReferenceSim, PackageScopedTypedefKeepsBlockLocalSigned) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  typedef byte sb_t;\n"
      "endpackage\n"
      "module t;\n"
      "  logic [31:0] y;\n"
      "  initial begin\n"
      "    pkg::sb_t s;\n"
      "    s = -1;\n"
      "    y = (s < 0) ? 1 : 2;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 1u);
}

// The same lookup answers what kind of type the name stands for, which is how
// a §6.16 string reached through a typedef is told from a bit vector. A block
// local declared with a package typedef of `string` answers len() as a string
// only when the simulator found the typedef behind its scoped name; as the
// 32-bit carrier it holds the four characters "abcde" does not fit in.
TEST(PackageScopeReferenceSim, PackageScopedTypedefMakesBlockLocalAString) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  typedef string str_t;\n"
      "endpackage\n"
      "module t;\n"
      "  logic [31:0] n;\n"
      "  initial begin\n"
      "    pkg::str_t s;\n"
      "    s = \"abcde\";\n"
      "    n = s.len();\n"
      "  end\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(val, 5u);
}

// §26.3: a wildcard import written in the module makes the package's class
// visible by its bare name, and §8.10 has its static method called through
// that name with no object. The call answers the method's 8; a class the
// import did not bind answers the zero of an unresolved call.
TEST(PackageImportSim, WildcardImportedClassStaticMethodCalledByBareName) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class plain_t;\n"
                      "    static function int get();\n"
                      "      return 8;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import p::*;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = plain_t::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            8u);
}

// §3.12.1: a name a module does not declare is searched for in the
// compilation-unit scope, including the names a package import there made
// visible; §26.3 has a wildcard import bring every name of the package. The
// import stands outside the module, so the module's own import list is empty
// and the class is bound only if the unit's import was applied.
TEST(PackageImportSim, UnitScopeWildcardImportBindsPackageClass) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class plain_t;\n"
                      "    static function int get();\n"
                      "      return 8;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "import p::*;\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = plain_t::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            8u);
}

// §26.3: the package scope resolution operator reaches a package's declaration
// with no import at all, and §8.23 has the class so reached prefix a static
// method call. Nothing imports `p`, so `p::pk_t::get()` answers 9 only if the
// package's class is lowered and bound under its qualified name regardless of
// any import.
TEST(PackageScopeReferenceSim, PackageQualifiedClassStaticMethodCall) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class pk_t;\n"
                      "    static function int get();\n"
                      "      return 9;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = p::pk_t::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            9u);
}

// §26.3 and §26.5: a class declared in the compilation-unit scope keeps its
// name over a same-named class that a wildcard import there would bring in,
// while the package's class stays reachable through its qualified name. The
// two static methods answer 8 and 9, so a lowering that bound either name to
// the other class is told apart from one that bound each to its own.
TEST(PackageScopeReferenceSim, UnitClassKeepsNameOverImportedPackageClass) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class same_t;\n"
                      "    static function int get();\n"
                      "      return 9;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "import p::*;\n"
                      "class same_t;\n"
                      "  static function int get();\n"
                      "    return 8;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = same_t::get() * 10 + p::same_t::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            89u);
}

// §26.3 (printed page 808) with §8.6 (printed 183): a method is called
// through a handle by the syntax a property is read by, and the handle may
// be a package's variable named through the package scope resolution
// operator, so `p1::h.m()` after `p1::h = new` runs C's m on p1's object:
// 3 * 7 = 21. The receiver of a method call was taken as an identifier
// alone, so the scoped receiver resolved no object and y stayed 0.
TEST(PackageScopeReferenceSim, PackageQualifiedHandleMethodCall) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v = 3;\n"
                      "    function int m();\n"
                      "      return v * 7;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::h = new;\n"
                      "    y = p1::h.m();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            21u);
}

// §26.3 (printed page 808) with §8.6 (printed 183) and §13.3: a task enabled
// through a package-qualified handle, `p1::h.t(5);`, runs C's t on p1's
// object, so the property it writes reads back through the same handle as 5.
// The statement's receiver was taken as an identifier alone, so the task ran
// on no object and the read answered 0.
TEST(PackageScopeReferenceSim, PackageQualifiedHandleTaskEnableWritesProperty) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "    task t(int a);\n"
                      "      v = a;\n"
                      "    endtask\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::h = new;\n"
                      "    p1::h.t(5);\n"
                      "    y = p1::h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            5u);
}

// §26.6 (printed page 815) with §8.6: a package's class-handle variable an
// export hands on takes a method call through the exporting package's
// qualifier as through the declaring one's, `p2::h.m()` after `import p1::h;
// export p1::h;` and `p2::h = new` running C's m on p1's object: 3 * 7 = 21.
// The exporter's key is bound to p1's storage and class record, but the
// scoped receiver was not taken, so y stayed 0.
TEST(PackageScopeReferenceSim, ExportedHandleMethodCallThroughTheExporter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v = 3;\n"
                      "    function int m();\n"
                      "      return v * 7;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::h;\n"
                      "  export p1::h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p2::h = new;\n"
                      "    y = p2::h.m();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            21u);
}

// §26.3 (printed page 808) with §8.6 (printed 183): a method called on the
// object a method call returned, `p1::h.self().m()`, runs on that object,
// the inner call being one through the package-qualified handle: 3 * 7 =
// 21. The inner call resolved no object, so the outer one had none to run
// on and y stayed 0.
TEST(PackageScopeReferenceSim, PackageQualifiedHandleMethodCallChained) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v = 3;\n"
                      "    function C self();\n"
                      "      return this;\n"
                      "    endfunction\n"
                      "    function int m();\n"
                      "      return v * 7;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::h = new;\n"
                      "    y = p1::h.self().m();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            21u);
}

// §26.3 (printed page 808) with §13.5.5 (printed 351): the parentheses after
// a void function or a task that takes no arguments are optional, so
// `p1::h.m;` and `p1::h.t;` through a package-qualified handle run C's m and
// t on p1's object: v = 8, then v = 8 + 30 = 38. The parenthesis-free
// statement's receiver was taken as an identifier alone, so the statement
// read m and t as properties and discarded the values, and y stayed 0.
TEST(PackageScopeReferenceSim,
     PackageQualifiedHandleParenthesisFreeMethodStatement) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "    function void m();\n"
                      "      v = 8;\n"
                      "    endfunction\n"
                      "    task t;\n"
                      "      v = v + 30;\n"
                      "    endtask\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::h = new;\n"
                      "    p1::h.m;\n"
                      "    p1::h.t;\n"
                      "    y = p1::h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            38u);
}

// §26.3 (printed page 808) with §18.7: randomize() called through a
// package-qualified handle, `p1::h.randomize()`, solves p1's object's
// constraints, so `r == 9` leaves r at 9 and the call answers 1: y = 19. The
// randomize receiver was taken as an identifier alone, so the scoped call
// resolved no object, drew nothing, and y stayed 0.
TEST(PackageScopeReferenceSim, PackageQualifiedHandleRandomize) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    rand bit [3:0] r;\n"
                      "    constraint c { r == 9; }\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::h = new;\n"
                      "    y = p1::h.randomize() * 10 + p1::h.r;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            19u);
}

// §26.3 (printed page 808) with §18.8 and §18.9: rand_mode() and
// constraint_mode() through a package-qualified handle, in the named form
// `p1::h.c.constraint_mode(...)` and the no-name form `p1::h.rand_mode(0)`,
// read and set p1's object's modes: both read 1 at first, 11, and 0 each
// once turned off, so y = 11 * 100 + 0 = 1100. The receivers were taken as
// an identifier alone -- the no-name scoped form read as an object p1's
// member h -- so nothing was resolved and y stayed 0.
TEST(PackageScopeReferenceSim,
     PackageQualifiedHandleRandModeAndConstraintMode) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    rand bit [3:0] r;\n"
                      "    constraint c { r == 9; }\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::h = new;\n"
                      "    y = p1::h.c.constraint_mode() * 10 + "
                      "p1::h.r.rand_mode();\n"
                      "    p1::h.c.constraint_mode(0);\n"
                      "    p1::h.rand_mode(0);\n"
                      "    y = y * 100 + p1::h.c.constraint_mode() * 10 + "
                      "p1::h.r.rand_mode();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            1100u);
}

// §26.3 (printed page 808) with §18.8 (printed 554-555): rand_mode() through
// a package-qualified handle in the element form, `p1::h.arr[1].rand_mode(0)`,
// names one element of p1's object's unpacked array member by its index, so
// arr[1], held at 9 and turned off, is a state variable that eight randomize
// calls leave at 9 while arr[0] is drawn under its constraint to 3, and the
// nonvoid form reads 0 for arr[1] and 1 for arr[0]: y = 8 * 1000 + 3 * 100 +
// 0 * 10 + 1 = 8301. An active arr[1] is drawn from sixteen values on each
// call, so it stays at 9 through all eight with a chance of one in 16^8. The
// element receiver was refused by every extractor, the scoped one taking
// the handle alone or a member access on it, so the call set nothing, the
// element was drawn with the rest and the queries answered nothing.
TEST(PackageScopeReferenceSim, PackageQualifiedHandleArrayElementRandMode) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    rand bit [3:0] arr[2];\n"
                      "    constraint c { arr[0] == 3; }\n"
                      "  endclass\n"
                      "  C h;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y, held = 0;\n"
                      "  initial begin\n"
                      "    p1::h = new;\n"
                      "    p1::h.arr[1] = 9;\n"
                      "    p1::h.arr[1].rand_mode(0);\n"
                      "    repeat (8) begin\n"
                      "      void'(p1::h.randomize());\n"
                      "      if (p1::h.arr[1] == 9) held++;\n"
                      "    end\n"
                      "    y = held * 1000 + p1::h.arr[0] * 100 + "
                      "p1::h.arr[1].rand_mode() * 10 + "
                      "p1::h.arr[0].rand_mode();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            8301u);
}

// §26.3 (printed page 808) with §7.10.2: a queue's methods called through
// the package-qualified name of a package's queue, `p1::q.push_back(4)`,
// `p1::q.push_back(6)` and `p1::q.size()`, act on p1's queue, so
// `p1::q[1] * 10 + p1::q.size()` reads 62. The queue call's scoped receiver
// was resolved as a class's static property alone, so nothing was pushed
// and y stayed 0. This also depends on the package queue's storage being
// created under the "p1.q" key (#313); until it is, the receiver names no
// queue.
TEST(PackageScopeReferenceSim, PackageQualifiedQueuePushBackAndSize) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int q[$];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::q.push_back(4);\n"
                      "    p1::q.push_back(6);\n"
                      "    y = p1::q[1] * 10 + p1::q.size();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            62u);
}

// §26.3 (printed page 810) makes an imported declaration visible under its
// unqualified name and §26.6 (printed 815) an export hand it on under the
// exporter's, and §15.3 (printed 372) gives a semaphore its bucket: the bare
// `s` after `import p1::s` and `p2::s` through p2's export are p1's one
// bucket of two keys, so a get through each leaves try_get through the
// qualifier nothing: 10. The import and the export aliased the Variable and
// the queue alone, so neither name found a bucket and both gets ran on none,
// leaving the two keys and reading 11.
TEST(PackageScopeReferenceSim, ImportedAndReExportedSemaphoreShareOneBucket) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  semaphore s = new(2);\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::s;\n"
                      "  export p1::s;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::s;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    s.get(1);\n"
                      "    p2::s.get(1);\n"
                      "    y = 10 + p1::s.try_get(1);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

// §9.7 (printed page 245 of ~/IEEE 1800-2023.pdf) lets a variable be declared
// of the built-in process class and has kill() forcibly terminate the process a
// handle names, whose status() then reads KILLED; §26.3 (printed 808) names
// a package's variable through the package scope resolution operator. The
// child assigns itself to p1's handle and would write 99 to x at #10, the
// kill at #1 stops it, and at #21 the status is KILLED and x still 0:
// 1 * 10 + 1. No class was recorded under "p1.proc", so the kill resolved no
// receiver, the child wrote 99 and finished, and status() answered no call:
// 0. A kill that landed with a status() that did not would read 1.
TEST(PackageScopeReferenceSim, PackageProcessHandleIsKilledAndReadsKilled) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  process proc;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int x = 0, y;\n"
                      "  initial begin\n"
                      "    fork\n"
                      "      begin\n"
                      "        p1::proc = process::self();\n"
                      "        #10 x = 99;\n"
                      "      end\n"
                      "    join_none\n"
                      "    #1;\n"
                      "    p1::proc.kill();\n"
                      "    #20;\n"
                      "    y = (p1::proc.status() == process::KILLED) * 10;\n"
                      "    y = y + (x == 0);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            11u);
}

// §9.7 (printed page 245): await() suspends the caller until the process the
// handle names terminates; §26.3 (printed 808) names a package's handle
// through the package scope resolution operator. The child sets a at #5, the
// parent awaits it from #1 and then copies a: 1. With no class recorded under
// "p1.proc" the await resolved no process, so the parent went on at #1 and
// copied the 0 a still held.
TEST(PackageScopeReferenceSim, PackageProcessHandleAwaitsTermination) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  process proc;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int a = 0, y;\n"
                      "  initial begin\n"
                      "    fork\n"
                      "      begin\n"
                      "        p1::proc = process::self();\n"
                      "        #5 a = 1;\n"
                      "      end\n"
                      "    join_none\n"
                      "    #1;\n"
                      "    p1::proc.await();\n"
                      "    y = a;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            1u);
}

// §26.2 (printed page 808) has a package's subroutines see the package's own
// typedefs, §13.3 (printed 337) declares a formal with any data_type, and
// §7.2.1 (printed 147) lays an inline union out member by member, `pair_t
// Add` naming a typedef of a structure of its own. The elaborator resolved a
// formal's typedef-named members for a module's subroutines alone, reached
// by its item walk, and a package's by nothing, so p's f was sized as if Add
// were a scalar: its layout gave Add no members to place `'{3, 4}` by or to
// read `a.Add.a` through, and `p::f(tagged Add '{3, 4})` answered 0 where
// §10.9.2 (printed 263) places 3 into a and 4 into b, 34.
TEST(PackageScopeReferenceSim,
     PackageFunctionInlineUnionFormalReadsANestedTypedefMember) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef struct { int a, b; } pair_t;\n"
                      "  function int f(union tagged { void None; pair_t Add; }"
                      " a);\n"
                      "    return a.Add.a * 10 + a.Add.b;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p::f(tagged Add '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            34u);
}

// §26.3 (printed page 808) names a package's declaration through the package
// scope resolution operator, and §26.2 (printed 808) has p's items see what p
// declares or imports and nothing of the compilation unit's, so with no import
// in p the member `q::pair_t Add` of f's formal resolves through q's qualifier
// alone. The parser read `q` as a member name and stopped at the `::`, and
// had it got further the member kept `pair_t` alone, a name p's table never
// held, so Add was sized as a scalar and `p::f(tagged Add '{3, 4})` had no
// members to place 3 and 4 in for `a.Add.a * 10 + a.Add.b`, 34.
TEST(PackageScopeReferenceSim,
     PackageFunctionInlineUnionFormalResolvesAnotherPackagesQualifiedMember) {
  EXPECT_EQ(RunAndGet("package q;\n"
                      "  typedef struct { int a, b; } pair_t;\n"
                      "endpackage\n"
                      "package p;\n"
                      "  function int f(union tagged { void None; q::pair_t "
                      "Add; } a);\n"
                      "    return a.Add.a * 10 + a.Add.b;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p::f(tagged Add '{3, 4});\n"
                      "endmodule\n",
                      "y"),
            34u);
}

// The same qualified member on a module variable's inline union: §26.3's
// `q::pair_t` names q's structure from a module that imports nothing, and
// §7.2.1 (printed 147) lays the union's Add member out by that structure, so
// a tagged assignment of `'{3, 4}` places 3 in a and 4 in b for `v.Add.a *
// 10 + v.Add.b` to read 34.
TEST(PackageScopeReferenceSim,
     ModuleVariableInlineUnionResolvesAPackageQualifiedMember) {
  EXPECT_EQ(RunAndGet("package q;\n"
                      "  typedef struct { int a, b; } pair_t;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  union tagged { void None; q::pair_t Add; } v;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    v = tagged Add '{3, 4};\n"
                      "    y = v.Add.a * 10 + v.Add.b;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            34u);
}

}  // namespace
