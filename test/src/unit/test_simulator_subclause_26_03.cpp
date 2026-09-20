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

// §26.3 with §23.2.4 and §7.2.1: a module variable declared with a
// package-scoped struct type, `pk::rec_t r;`, is a variable of that struct,
// so a member write lands in the member's bits and a member read after a
// whole-variable write reads them. The elaborator sized the variable through
// the `pk::rec_t` key but took its struct layout from the bare name, which
// the module's typedef table does not hold, so the members were never laid
// out: `r.id = 7` was dropped and `r.id` read 0. The result packs the whole
// value after the member writes (07012c) with the id read after the whole
// write (7): 24'h07012c * 16 + 7.
TEST(PackageScopeReferenceSim, PackageScopedStructVariableHasItsMembers) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  typedef struct packed {\n"
                      "    logic [7:0] id;\n"
                      "    logic [15:0] val;\n"
                      "  } rec_t;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  pk::rec_t r;\n"
                      "  logic [31:0] result;\n"
                      "  initial begin\n"
                      "    r.id = 7;\n"
                      "    r.val = 300;\n"
                      "    result = r * 16;\n"
                      "    r = 24'h07012c;\n"
                      "    result = result + r.id;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0x07012c * 16u + 7u);
}

// §26.3 (printed page 808 of ~/LRM.pdf): a declaration made in a package is
// referenced through the package scope resolution operator, the subclause's
// own example being a function call, `ComplexPkg::mul(a, b)`. A package
// function called through its scoped name was looked up under the empty
// callee a scoped call carries, found nothing and answered 0, while the same
// function under an import ran. No import here, so the bare name is never
// bound: the value comes through `pk::` alone. mix(6) is 6 * 6 + 1 = 37 and
// mix(3) is 10, so a call answering 0 or the argument itself reads apart.
TEST(PackageScopeReferenceSim, PackageFunctionCalledThroughItsScopedName) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  function automatic int mix(int n);\n"
                      "    return n * n + 1;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module t;\n"
                      "  logic [31:0] y;\n"
                      "  initial y = pk::mix(6) * 100 + pk::mix(3);\n"
                      "endmodule\n",
                      "y"),
            3710u);
}

// §26.3 with §13.4: the scoped call stands inside a class method's expression
// as well, where the method interpreter evaluates it; the class is declared
// at compilation-unit scope, outside every import.
TEST(PackageScopeReferenceSim,
     PackageFunctionCalledThroughItsScopedNameInAClassMethod) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  function automatic int mix(int n);\n"
                      "    return n * n + 1;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "class U;\n"
                      "  function int via(int k);\n"
                      "    return pk::mix(k) + 1000;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  logic [31:0] y;\n"
                      "  initial begin\n"
                      "    U u = new;\n"
                      "    y = u.via(4);\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            1017u);
}

// §26.3 with §13.5.4: a package void function enabled as a statement through
// the package scope, its output argument bound by name and then by position.
// The statement was dropped whole, so the outputs stayed 0.
TEST(PackageScopeReferenceSim,
     PackageVoidFunctionEnabledThroughItsScopedNameWritesItsOutput) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  function automatic void pf(input int n = 1,\n"
                      "                             output int r);\n"
                      "    r = n * 3;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int a, b;\n"
                      "  logic [31:0] y;\n"
                      "  initial begin\n"
                      "    pk::pf(.r(a), .n(9));\n"
                      "    pk::pf(4, b);\n"
                      "    y = a * 100 + b;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            2712u);
}

// §26.3 and §3.12.1: a package class made visible by a wildcard import written
// at compilation-unit scope is a class type in the following class declaration
// and module, so `B h` holds a handle, `h = d` assigns a subclass handle to it
// (§8.13), and `h.who()` dispatches to D's override (§8.20) -- 2 * 10 + 3.
TEST(PackageImportSim, CuScopeWildcardImportedClassAsBaseHandleType) {
  auto val = RunAndGet(
      "package pk;\n"
      "  class B; int b = 3;\n"
      "    virtual function int who(); return 1; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "import pk::*;\n"
      "class D extends B;\n"
      "  virtual function int who(); return 2; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r;\n"
      "  B h; D d = new;\n"
      "  initial begin\n"
      "    h = d;\n"
      "    r = h.who() * 10 + d.b;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 23u);
}

// §26.3 has a package's declarations visible throughout the package, and §13.4
// a function read the variables of the scope it is declared in, so a package
// function reads the package's own variable by its bare name: `pk::get()`
// answers `base`, 30, and a write in `pk::set` lands on the same variable, so
// the second read is 31. The variable is held under "pk.base" and the body
// asked for "base", which no scope answered, so both reads were 0.
TEST(PackageScopeReferenceSim,
     PackageFunctionReadsAndWritesItsPackageVariable) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  int base = 30;\n"
                      "  function automatic int get(); return base;\n"
                      "  endfunction\n"
                      "  function automatic void set(int v); base = v;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    out = pk::get() * 100;\n"
                      "    pk::set(31);\n"
                      "    out = out + pk::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            30u * 100u + 31u);
}

// §26.3: a wildcard import written in a package makes another package's
// variable visible to the importing package's functions by its bare name --
// `pq::get()` reads pk's `base` through pq's `import pk::*`.
TEST(PackageScopeReferenceSim, PackageFunctionReadsAVariableItsPackageImports) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  int base = 30;\n"
                      "endpackage\n"
                      "package pq;\n"
                      "  import pk::*;\n"
                      "  function automatic int get(); return base;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial out = pq::get();\n"
                      "endmodule\n",
                      "out"),
            30u);
}

// §13.5.3 evaluates a default actual in the scope of the subroutine's
// declaration, so `int v = base` of a package function reads the package's
// base, 30, and not the caller's module variable of the same name, 1; an
// actual the caller writes, `pk::get(base)`, is the caller's expression and
// reads the module's 1 (§13.5) -- 30 * 10 + 1.
TEST(PackageScopeReferenceSim, PackageFunctionDefaultReadsThePackageScope) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  int base = 30;\n"
                      "  function automatic int get(int v = base); return v;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int base = 1;\n"
                      "  int out;\n"
                      "  initial out = pk::get() * 10 + pk::get(base);\n"
                      "endmodule\n",
                      "out"),
            30u * 10u + 1u);
}

// §6.19 makes an enumeration's members constants of the scope the enumeration
// is written in and §26.3 references a package's declaration through the
// package scope resolution operator (printed pages 119 and 808 of ~/LRM.pdf),
// so `pk::HIGH` is the package's constant from a module that imports nothing,
// as `pk::P` is its parameter. A package's parameters had storage under their
// scoped key and its enumeration constants none, so the read answered 0. HIGH
// is 3 and B follows A, which §6.20.1 lets name the package's parameter, at
// BASE + 2: 3 * 100 + 7. A constant folded without the package's parameters
// would read 301, and one with no storage 0.
TEST(PackageScopeReferenceSim, PackageEnumConstantReadThroughItsScope) {
  EXPECT_EQ(RunAndGet("package pk;\n"
                      "  parameter int BASE = 5;\n"
                      "  typedef enum {LOW, MED = 2, HIGH} sev_t;\n"
                      "  typedef enum {A = BASE + 1, B} step_t;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial out = pk::HIGH * 100 + pk::B;\n"
                      "endmodule\n",
                      "out"),
            307u);
}

}  // namespace
