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

// §26.3 (printed page 808 of ~/LRM.pdf) references a package's declarations
// through the package name whether or not the package was imported, and §6.18
// (printed page 118) makes an object declared with a typedef's name an object
// of the type the name stands for. A `pkg::nib_t v;` written as a block item
// of a sequential block is sized at run time from the design's type_widths
// table, which the elaborator keys by "pkg::nib_t" and which the simulator
// looked up by "nib_t" alone, so v was created at the 32-bit carrier that
// stands in for a type nothing could size: v = -1 read 4294967295 and $bits(v)
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

}  // namespace
