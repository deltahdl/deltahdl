#include <gtest/gtest.h>

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

// §26.3 (printed page 808 of ~/IEEE 1800-2023.pdf): a declaration made in a
// package is referenced through the package scope resolution operator, the
// subclause's own example being a function call, `ComplexPkg::mul(a, b)`. A
// package function called through its scoped name was looked up under the empty
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
// package scope resolution operator (printed pages 119 and 808 of ~/IEEE
// 1800-2023.pdf), so `pk::HIGH` is the package's constant from a module that
// imports nothing, as `pk::P` is its parameter. A package's parameters had
// storage under their scoped key and its enumeration constants none, so the
// read answered 0. HIGH is 3 and B follows A, which §6.20.1 lets name the
// package's parameter, at BASE + 2: 3 * 100 + 7. A constant folded without the
// package's parameters would read 301, and one with no storage 0.
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

// §26.3 (printed page 808 of ~/IEEE 1800-2023.pdf) names a package's variable
// through the package scope resolution operator, and §8.7 has `new` construct
// an object of the class the target is declared with -- the issue's probes 114
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

// §8.25 (printed page 203 of ~/IEEE 1800-2023.pdf) with §26.2 (printed 808): a
// package variable declared with a specialization, `G #(5) b;`, is a handle of
// that specialization, and the object `p1::b = new` constructs through the
// package scope resolution operator binds N to 5, which a method of the object
// reads. The lowerer recorded the package variable's class under "p1.b" and
// dropped its `#(5)`, which only a module's declaration recorded, so the object
// was built as the default specialization and get_n() read 1. A second variable
// declared bare beside it reads the default, so the pair packs 5 * 10 + 1;
// 11 would say the specialization was still dropped and 55 that the default
// was bound wrongly.
TEST(PackageScopeReferenceSim,
     ScopedPackageClassVariableConstructedWithItsSpecialization) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class G #(int N = 1);\n"
                      "    function int get_n();\n"
                      "      return N;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "  G #(5) b;\n"
                      "  G d;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::b = new;\n"
                      "    p1::d = new;\n"
                      "    y = p1::b.get_n() * 10 + p1::d.get_n();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            51u);
}

// §26.3 with A.2.8: a package import declaration is a block item declaration,
// so a function body may open with one, and the import makes the package's
// declarations visible in that body without a package name qualifier (printed
// page 809). A wildcard import written as the body's first item binds both the
// package's parameter and its function: `K * five()` is 8 * 5. Before the fix
// neither name resolved and the function returned 0, so 40 is read only when
// both bind; 0 or 8 would say one of them still fails.
TEST(PackageImportSim, WildcardImportInAFunctionBodyBindsItsNames) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  parameter int K = 8;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    return K * five();\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            40u);
}

// §26.3: an explicit import makes exactly the symbol it names visible, and the
// body's own scope is searched before the module's (printed page 810), so `K`
// read in k() is p's 8 through `import p::K` although the module declares a
// `K` of 2, and f(), automatic rather than static, reaches p's five() through
// its own wildcard import. calc() combines the two. 8 * 1000 + 5 * 100 + 40 is
// 8540; a body whose import did not shadow the module's K would read 2540.
TEST(PackageImportSim, ExplicitAndWildcardImportsInSeparateFunctionBodies) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  parameter int K = 8;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int K = 2;\n"
                      "  function int k(); import p::K; return K; endfunction\n"
                      "  function automatic int f();\n"
                      "    import p::*;\n"
                      "    return five();\n"
                      "  endfunction\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    return K * five();\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = k() * 1000 + f() * 100 + calc();\n"
                      "endmodule\n",
                      "out"),
            8540u);
}

// §26.3 with §13.3: the import stands in an automatic task body that suspends
// on a delay before it reads the imported names, so the binding must survive
// the suspension: `#3 r = trip(K)` is 10 * 3 at time 3, and the caller reads
// r * 10 + $time as 303. A task whose body import were lost at the delay
// would answer 3, and one that never bound the names 0 * 10 + 3.
TEST(PackageImportSim, WildcardImportInATaskBodyOutlivesItsDelay) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  parameter int K = 10;\n"
                      "  function int trip(int a); return a * 3; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  task automatic t(output int r);\n"
                      "    import p::*;\n"
                      "    #3 r = trip(K);\n"
                      "  endtask\n"
                      "  int r;\n"
                      "  int out;\n"
                      "  initial begin\n"
                      "    t(r);\n"
                      "    out = r * 10 + $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            303u);
}

// §26.6: `export p1::x` in p2 makes p1's x, which p2 imported explicitly,
// available to a wildcard import of p2 (printed page 815), so the module
// reads the original variable's 6 beside p2's own y of 7: 67. Without the
// export the elaborator reports x, and a lowering that bound x to nothing
// would read 7.
TEST(PackageImportSim, ExplicitlyExportedVariableReadThroughAWildcardImport) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x = 6;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::x;\n"
                      "  export p1::x;\n"
                      "  int y = x + 1;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p2::*;\n"
                      "  int out;\n"
                      "  initial out = x * 10 + y;\n"
                      "endmodule\n",
                      "out"),
            67u);
}

// §26.6: `export *::*` exports every declaration p2 imported, from every
// package it imports; the explicitly imported x of p1 is one, so the same
// read answers 67 through it.
TEST(PackageImportSim, StarStarExportedVariableReadThroughAWildcardImport) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x = 6;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::x;\n"
                      "  export *::*;\n"
                      "  int y = x + 1;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p2::*;\n"
                      "  int out;\n"
                      "  initial out = x * 10 + y;\n"
                      "endmodule\n",
                      "out"),
            67u);
}

// §26.3 (printed page 810): a function call is resolved against the locally
// visible identifiers of the current scope first and then the potentially
// locally visible ones a wildcard import of that scope supplies, the outer
// scope searched only after both; a body's `import p::*` makes p's five
// potentially locally visible in the body, so `five()` written there is p's,
// 5, ahead of the module's own five of 50 in the enclosing scope. A lookup
// that asked the module's registrations before the body's imports answered
// 50.
TEST(PackageImportSim, BodyImportedFunctionShadowsTheModulesOfTheSameName) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    return five();\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            5u);
}

// §26.3 with §23.6: the same body in an instance below the top, whose own
// five is registered under the instance's prefix ahead of the bare name; the
// body's import still stands ahead of the instance's declaration, so the
// read is 5 and not the instance's 50.
TEST(PackageImportSim, BodyImportedFunctionShadowsTheInstancesOfTheSameName) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module child(output int o);\n"
                      "  function int five(); return 50; endfunction\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    return five();\n"
                      "  endfunction\n"
                      "  initial o = calc();\n"
                      "endmodule\n"
                      "module top;\n"
                      "  int out;\n"
                      "  child u1(.o(out));\n"
                      "endmodule\n",
                      "out"),
            5u);
}

// §26.3: the import's visibility is the importing body's alone, so a second
// body of the same module with no import of its own finds no five nearer
// than the module's and reads 50. A lookup that let one body's import leak
// into every body of the module would answer 5.
TEST(PackageImportSim, BodyWithoutImportCallsTheModulesFunctionOfTheSameName) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    return five();\n"
                      "  endfunction\n"
                      "  function int plain(); return five(); endfunction\n"
                      "  int out;\n"
                      "  initial out = calc() * 100 + plain();\n"
                      "endmodule\n",
                      "out"),
            550u);
}

// §26.3 with §23.8.1: a package function's body is searched through its own
// package's scope first, and where the package neither declares nor imports
// the name the search goes on outward and upward, so `base()` written in
// p's twice reaches the module's base of 21 that the package never names:
// 42. A package-scope lookup that answered "not found" instead of handing
// on to the module's registrations would call nothing and read 0.
TEST(PackageScopeReferenceSim,
     PackageFunctionCallsAModuleFunctionItsPackageNeverNames) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int twice(); return base() * 2; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int base(); return 21; endfunction\n"
                      "  int out;\n"
                      "  initial out = p::twice();\n"
                      "endmodule\n",
                      "out"),
            42u);
}

// §26.3 makes a wildcard import's names visible throughout the importing scope
// (printed page 810), and §6.8 sets a variable's initial value as part of its
// declaration (printed 106), a reference that scope makes, so `int z = x;`
// beside `import p1::*` reads p1's x as `int y = p1::x;` does -- the Clause 26
// discovery's probe 129. The imports were bound after the module's variables
// had been lowered, so z read 0 while y read 6: z * 10 + y is 66 against the 6
// of an unbound z.
TEST(PackageImportSim, WildcardImportedVariableReadByADeclarationInitializer) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x = 6;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int z = x;\n"
                      "  int y = p1::x;\n"
                      "  int out;\n"
                      "  initial out = z * 10 + y;\n"
                      "endmodule\n",
                      "out"),
            66u);
}

// The explicit form of the same read, `import p1::x; int z = x + 1;`, which
// read 1 for the same reason: 7 tells the bound x from an unbound one.
TEST(PackageImportSim,
     ExplicitlyImportedVariableReadByADeclarationInitializer) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x = 6;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::x;\n"
                      "  int z = x + 1;\n"
                      "endmodule\n",
                      "z"),
            7u);
}

// §26.6's own packages and module (printed pages 815-816): p2 exports p1's x
// under `import p1::x; export p1::*;`, p4 under `import p1::*; export p1::*;`
// beside its own `int y = x;`, and top imports both by wildcard and declares
// `int z = x;`. §26.6 makes an import of a declaration reached through an
// export an import of the original declaration, so x reached by two exported
// paths is one candidate and no §26.3 conflict -- the discovery's probes 45
// and 130, which read 0 or were reported. z * 10 + y is 66; RunAndGet also
// holds the elaboration clean, so an ambiguity report fails it.
TEST(PackageImportSim, VariableReachedByTwoExportPathsReadByAnInitializer) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x = 6;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::x;\n"
                      "  export p1::*;\n"
                      "endpackage\n"
                      "package p4;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "  int y = x;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p2::*;\n"
                      "  import p4::*;\n"
                      "  int z = x;\n"
                      "  int out;\n"
                      "  initial out = z * 10 + y;\n"
                      "endmodule\n",
                      "out"),
            66u);
}

// §26.5's Table 26-1: a declaration of the importing scope takes the name
// over a wildcard import of it, and the imports now bind before the module's
// variables exist, so the module's own x must still win: x * 100 + p1::x is
// 306, where an import left in place of the declaration would read 606.
TEST(PackageImportSim, AModulesOwnDeclarationShadowsAnImportInAnInitializer) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x = 6;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int x = 3;\n"
                      "  int z = x * 100 + p1::x;\n"
                      "endmodule\n",
                      "z"),
            306u);
}

// An instance writes its own imports (§26.3), and its declaration
// initializers are evaluated under its prefix, so the binding is made before
// the instance's variables as it is for the top: u.z reads p1's 6 through the
// child's wildcard import, and v.z reads the child's own x of 3 over the
// import it also writes (§26.5) -- 6 * 10 + 3.
TEST(PackageImportSim, ChildInstanceInitializerReadsItsOwnImport) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x = 6;\n"
                      "endpackage\n"
                      "module reader;\n"
                      "  import p1::*;\n"
                      "  int z = x;\n"
                      "endmodule\n"
                      "module owner;\n"
                      "  import p1::*;\n"
                      "  int x = 3;\n"
                      "  int z = x;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  reader u();\n"
                      "  owner v();\n"
                      "  int out;\n"
                      "  initial out = u.z * 10 + v.z;\n"
                      "endmodule\n",
                      "out"),
            63u);
}

// §26.3's top2 (printed page 809) imports q's FALSE explicitly beside p's
// wildcard, and its `teeth_t myteeth` is here given the literal as its
// declaration initializer: `teeth_t a = FALSE;` reads q's FALSE, 4 with
// ORIGINAL at 3, where p's FALSE and an unbound name both read 0; b's TRUE
// says the wildcard's literal still initializes a declaration -- 4 * 10 + 1.
TEST(PackageImportSim, ExplicitlyImportedEnumLiteralInitializesADeclaration) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  typedef enum { FALSE, TRUE } bool_t;\n"
                      "endpackage\n"
                      "package q;\n"
                      "  typedef enum { ORIGINAL = 3, FALSE } teeth_t;\n"
                      "endpackage\n"
                      "module top2;\n"
                      "  import p::*;\n"
                      "  import q::teeth_t, q::ORIGINAL, q::FALSE;\n"
                      "  teeth_t a = FALSE;\n"
                      "  bool_t b = TRUE;\n"
                      "  int out;\n"
                      "  initial out = a * 10 + b;\n"
                      "endmodule\n",
                      "out"),
            41u);
}

// §15.3.1 (printed page 373 of ~/IEEE 1800-2023.pdf) with §26.3 (printed 808):
// a package's `semaphore t`, declared with no initializer, is created by the
// procedural `p1::t = new(1)` as a bucket of one key, so the first try_get(1)
// procures it and the second finds the bucket empty: 1 * 10 + 0. The
// statement's target, the package scope resolution `p1::t`, was taken as an
// identifier alone by TrySemaphoreNewAssign, no class record stands under
// "p1.t" for TryClassNewAssign, and the statement fell to the generic store,
// leaving the bucket at its declared zero and both try_get() calls answering
// 0. The blocking get() is kept out so an unfilled bucket reads 0 rather
// than suspending the test.
TEST(PackageScopeReferenceSim, PackageSemaphoreConstructedByScopedNew) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  semaphore t;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int a, b, y;\n"
                      "  initial begin\n"
                      "    p1::t = new(1);\n"
                      "    a = p1::t.try_get(1);\n"
                      "    b = p1::t.try_get(1);\n"
                      "    y = a * 10 + b;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

// §15.3.1 (printed page 373) with §15.3.4 (printed 374) and §26.3 (printed
// 808): the key count `p1::t = new(3)` names is the whole bucket, so three
// try_get(1) calls procure a key each and a fourth procures none:
// 1 * 1000 + 1 * 100 + 1 * 10 + 0. A bucket of one would read 1000, and the
// unfilled bucket of the defect 0.
TEST(PackageScopeReferenceSim, ScopedNewKeyCountFillsThePackageSemaphore) {
  EXPECT_EQ(
      RunAndGet("package p1;\n"
                "  semaphore t;\n"
                "endpackage\n"
                "module top;\n"
                "  int y;\n"
                "  initial begin\n"
                "    p1::t = new(3);\n"
                "    y = p1::t.try_get(1) * 1000 + p1::t.try_get(1) * 100 +\n"
                "        p1::t.try_get(1) * 10 + p1::t.try_get(1);\n"
                "  end\n"
                "endmodule\n",
                "y"),
      1110u);
}

}  // namespace
