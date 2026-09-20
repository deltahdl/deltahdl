#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

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

// §26.3 names a package variable through the package scope resolution
// operator as an lvalue, and §11.4.1 and §11.4.2 have an assignment operator
// and an increment be blocking assignments to it, so `p::shared += 150` and
// `p::shared++` update the package's variable: 100 + 150 + 1 = 251. The plain
// `p::shared = v` landed and the operator forms wrote nothing, so the read
// through the scope stayed 100.
TEST(PackageScopeReferenceSim, CompoundAssignmentToAScopedPackageVariable) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int shared = 100;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    p::shared += 150;\n"
                      "    p::shared++;\n"
                      "    out = p::shared;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            251u);
}

// The same operators written inside a class method (the issue's probe 88):
// bump adds 150, inc adds 1 -- read after each, 250 * 1000 + 251.
TEST(PackageScopeReferenceSim,
     CompoundAssignmentToAScopedPackageVariableInAMethod) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int shared = 100;\n"
                      "endpackage\n"
                      "class Writer;\n"
                      "  function void bump(int n); p::shared += n;\n"
                      "  endfunction\n"
                      "  function void inc(); p::shared++; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    Writer w = new;\n"
                      "    w.bump(150);\n"
                      "    out = p::shared * 1000;\n"
                      "    w.inc();\n"
                      "    out = out + p::shared;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            250u * 1000u + 251u);
}

// §6.8 gives a variable declared with no initializer its type's default and
// makes it an assignment target, and §26.3 names a package's variable through
// the package scope resolution operator and through an import. A package
// variable declared without an initializer, `int pn;`, was given no storage
// at all, so `P::pn = 17` landed nowhere and pn read 0 by both names; with
// storage the write is read through both, 17 * 100 + 17, and the bare write
// `pn = 23` is read back through the scope, + 23.
TEST(PackageScopeReferenceSim, PackageVariableWithoutInitializerIsWritable) {
  EXPECT_EQ(RunAndGet("package P;\n"
                      "  int pn;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import P::*;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    P::pn = 17;\n"
                      "    out = P::pn * 100 + pn;\n"
                      "    pn = 23;\n"
                      "    out = out * 100 + P::pn;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            (17u * 100u + 17u) * 100u + 23u);
}

// The declared type goes with the storage: a package `string ps` holds the
// whole text written to it, len() 5, and a `logic pl` starts unknown while
// an `int` starts 0 (§6.8 Table 6-7) -- 5 * 100 + 1 * 10 + 0.
TEST(PackageScopeReferenceSim, PackageVariableWithoutInitializerKeepsItsType) {
  EXPECT_EQ(RunAndGet("package P;\n"
                      "  logic pl; int pn; string ps;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    P::ps = \"name2\";\n"
                      "    out = P::ps.len() * 100 + $isunknown(P::pl) * 10 +\n"
                      "          (P::pn == 0 ? 0 : 1);\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            510u);
}

// §26.2 performs a package variable's declaration assignment before any
// initial procedure starts, and its initializer may call a function of the
// package by its bare name or one a wildcard import brings in (§26.3): p's
// `int v = sq(8)` and q's `int w = sq(8)` through `import p::*` both read 64.
// The variables were initialized before the package's subroutines were
// registered and with no package in scope for the bare name, so both read 0;
// a later variable of the package reading an earlier one, `int u = v + 1`,
// is covered beside them -- 64 * 10000 + 64 * 100 + 65.
TEST(PackageScopeReferenceSim,
     PackageVariableInitializedFromAPackageFunctionCall) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int sq(int a); return a * a; endfunction\n"
                      "  int v = sq(8);\n"
                      "  int u = v + 1;\n"
                      "endpackage\n"
                      "package q;\n"
                      "  import p::*;\n"
                      "  int w = sq(8);\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial out = p::v * 10000 + q::w * 100 + p::u;\n"
                      "endmodule\n",
                      "out"),
            64u * 10000u + 64u * 100u + 65u);
}

// §26.3's own `import q::teeth_t, q::ORIGINAL, q::FALSE;` (printed page 809):
// an explicit import names an enumeration literal, which §6.19 makes a
// constant of the package and not an item of it, so LowerImportedName in
// src/simulator/lowerer_import.cpp found nothing to bind and the bare FALSE
// read 0. The second literal is the one read, 1 telling the binding from
// nothing bound and from ORIGINAL -- 1 * 10 + 1.
TEST(PackageImportSim, ExplicitImportOfAnEnumLiteralReadsItsValue) {
  EXPECT_EQ(RunAndGet("package q;\n"
                      "  typedef enum { ORIGINAL, FALSE } teeth_t;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import q::teeth_t, q::FALSE;\n"
                      "  teeth_t a;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    a = FALSE;\n"
                      "    out = a * 10 + FALSE;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            11u);
}

// §26.3 searches a scope's locally visible identifiers, an explicit import's
// among them, before the candidates a wildcard import supplies (printed page
// 810), the clause's top2 module reading q's FALSE over p's. The wildcard's
// literal was emitted as a module variable ahead of the import lowering and
// held the name, so FALSE read p's 0; ORIGINAL is given 3 so that q's FALSE, 4,
// and ORIGINAL itself are each told from an unbound name, and TRUE says the
// wildcard still supplies the literal no explicit import names --
// 4 * 100 + 3 * 10 + 1.
TEST(PackageImportSim, ExplicitImportOfAnEnumLiteralShadowsAWildcardsLiteral) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef enum { FALSE, TRUE } bool_t;\n"
                      "endpackage\n"
                      "package q;\n"
                      "  typedef enum { ORIGINAL = 3, FALSE } teeth_t;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import p::*;\n"
                      "  import q::teeth_t, q::ORIGINAL, q::FALSE;\n"
                      "  teeth_t myteeth;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    myteeth = FALSE;\n"
                      "    out = myteeth * 100 + ORIGINAL * 10 + TRUE;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            431u);
}

// §26.3: `p::BLUE` names p's enumeration literal from any scope, with the
// literal's type, so §6.19.3 asks no cast of `c = p::BLUE` for a variable of
// that type, and the literal is its value wherever an integral is read. The
// elaborator took the scoped name for an integer and rejected c2's assignment,
// which RunAndGet reports; each scoped read also carries its own value, BLUE 2
// and GREEN 1, so a read that finds no storage answers 0 in its digit --
// 2 * 1000 + 2 * 100 + 1 * 10 + 2.
TEST(PackageScopeReferenceSim, ScopedEnumLiteralAssignedToAVariableOfItsType) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef enum { RED, GREEN, BLUE } color_t;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import p::*;\n"
                      "  color_t c1, c2;\n"
                      "  int i, j, out;\n"
                      "  initial begin\n"
                      "    c1 = BLUE;\n"
                      "    c2 = p::BLUE;\n"
                      "    i = p::GREEN;\n"
                      "    j = int'(p::BLUE);\n"
                      "    out = c1 * 1000 + c2 * 100 + i * 10 + j;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            2212u);
}

// The same literal through the scope alone, no import in force, into a
// variable whose type is named through the scope as well: `c = p::BLUE` left c
// 0. 2 is BLUE's value and neither RED's nor an unbound name's.
TEST(PackageScopeReferenceSim, ScopedEnumLiteralAssignedWithoutAnImport) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef enum { RED, GREEN, BLUE } color_t;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  p::color_t c;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    c = p::BLUE;\n"
                      "    out = c;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            2u);
}

// §12.5 compares the case expression with each case item's value, and §26.3
// makes `p::TWO` that value where a bare TWO is; the scoped item never matched
// and the default was taken. The default writes 7 and the item 2, so a case
// that matches nothing and one that matches the wrong item are each told from
// the match.
TEST(PackageScopeReferenceSim, ScopedEnumLiteralMatchesAsACaseItem) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef enum { ONE = 1, TWO, THREE } num_t;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import p::*;\n"
                      "  num_t n;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    n = TWO;\n"
                      "    case (n)\n"
                      "      ONE: out = 1;\n"
                      "      p::TWO: out = 2;\n"
                      "      THREE: out = 3;\n"
                      "      default: out = 7;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            2u);
}

// §26.3 (printed page 808 of ~/LRM.pdf) names a package's variable through
// the package scope resolution operator, and §8.7 has `new` construct an
// object of the class the target is declared with -- the issue's probes 114
// and 69: `p::global_h = new` from a module initial and from a method of a
// module-level class, the property written and read through the scope. The
// package's storage under "p.global_h" had no class recorded and the `new`
// assignment took no scoped target, so the handle stayed null and the property
// read 0 by both routes. The initial's object reads 35 and non-null 1, and the
// method's, constructed only after the handle is set null again so that a
// write landing on the initial's object cannot stand in for it, 27:
// 351 * 100 + 27.
TEST(PackageScopeReferenceSim, ScopedPackageClassVariableConstructedWithNew) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "  endclass\n"
                      "  C global_h;\n"
                      "endpackage\n"
                      "class Setter;\n"
                      "  function void go();\n"
                      "    p::global_h = new;\n"
                      "    p::global_h.v = 27;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    Setter s = new;\n"
                      "    p::global_h = new;\n"
                      "    p::global_h.v = 35;\n"
                      "    out = p::global_h.v * 10 + (p::global_h != null);\n"
                      "    p::global_h = null;\n"
                      "    s.go();\n"
                      "    out = out * 100 + p::global_h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            351u * 100u + 27u);
}

}  // namespace
