#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §26.3 (printed pages 810-811, Example 1): a reference inside a scope
// nested in the importing one is searched outward, first among the outer
// scope's locally visible identifiers and then among its wildcard candidates,
// so `x = 1` in the conditional generate block `b` writes p::x, and §27.5
// makes the block a scope of its own rather than a boundary. The block both
// writes and reads the import: `x = 1`, `y = 4` beside it on the module's
// own variable, and `z = x * 10 + k` reading the written x and the package's
// initialized k -- 17. The module reads all three after the block is done:
// 4 * 1000 + 1 * 100 + 17. A block whose write never reached p::x reads
// 4 * 1000 + 0 * 100 + (0 * 10 + 7) = 4007 instead.
TEST(PackageImportSim,
     WildcardImportReachesAProcessInsideAConditionalGenerateBlock) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int x;\n"
                      "  int k = 7;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p::*;\n"
                      "  int y, z;\n"
                      "  if (1) begin : b\n"
                      "    initial x = 1;\n"
                      "    initial y = 4;\n"
                      "    initial #1 z = x * 10 + k;\n"
                      "  end\n"
                      "  initial #2 y = y * 1000 + p::x * 100 + z;\n"
                      "endmodule\n",
                      "y"),
            4117u);
}

// §26.3 with §27.4: every instance of a loop generate block is a scope nested
// in the module, so each instance's process resolves the wildcard-imported x
// through the module's import and adds its own index's share, (g + 1) * 10
// for g of 0, 1 and 2 -- 60 once all three have run, and 0 where the block's
// write never reached the package variable.
TEST(PackageImportSim, WildcardImportReachesEachLoopGenerateBlockInstance) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int x;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p::*;\n"
                      "  int y;\n"
                      "  genvar g;\n"
                      "  for (g = 0; g < 3; g++) begin : blk\n"
                      "    initial x = x + (g + 1) * 10;\n"
                      "  end\n"
                      "  initial #1 y = p::x;\n"
                      "endmodule\n",
                      "y"),
            60u);
}

// §26.3 with §23.9: the import belongs to the child module c, whose
// generate blocks are nested in the instance u1, so their processes resolve
// the imported x through u1's own binding: the conditional block writes 5,
// the two loop instances add 1 and 2 at #1, and the conditional block reads
// the result, 8, into the child's own variable at #2. The top module, which
// imports nothing, reads the package variable through its scope and the
// child's variable by its hierarchical name -- 8 * 100 + 8.
TEST(PackageImportSim, ChildInstanceImportReachesItsOwnGenerateBlocks) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int x;\n"
                      "endpackage\n"
                      "module c;\n"
                      "  import p::*;\n"
                      "  int seen;\n"
                      "  if (1) begin : b\n"
                      "    initial x = 5;\n"
                      "    initial #2 seen = x;\n"
                      "  end\n"
                      "  genvar g;\n"
                      "  for (g = 0; g < 2; g++) begin : blk\n"
                      "    initial #1 x = x + g + 1;\n"
                      "  end\n"
                      "endmodule\n"
                      "module top;\n"
                      "  c u1();\n"
                      "  int y;\n"
                      "  initial #3 y = p::x * 100 + u1.seen;\n"
                      "endmodule\n",
                      "y"),
            808u);
}

// §26.3 (printed page 811, Example 1's line 4) with §23.9: a declaration the
// generate block makes is the locally visible identifier of the innermost
// scope, found before the search reaches the module's wildcard candidates,
// so the block's `x = 9` writes top.b.x and p::x keeps its initial 3. The
// block copies its own x out to the module's `out` (9) and the module reads
// p::x beside it: 3 * 10 + 9. A block whose write went to the import would
// read 9 * 10 + 9 = 99.
TEST(PackageImportSim,
     GenerateBlockDeclarationShadowsTheModulesWildcardImport) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int x = 3;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p::*;\n"
                      "  int out, y;\n"
                      "  if (1) begin : b\n"
                      "    int x;\n"
                      "    initial begin\n"
                      "      x = 9;\n"
                      "      out = x;\n"
                      "    end\n"
                      "  end\n"
                      "  initial #1 y = p::x * 10 + out;\n"
                      "endmodule\n",
                      "y"),
            39u);
}

// §26.3 (printed page 810) with §23.9 (printed 761): a function is a scope of
// its own, nested in the module that declares it and not in whichever body
// calls it, so `five()` written in plain() -- a body with no import -- is
// searched in plain's scope and then the module's, and is the module's 50
// even when calc(), whose body imports p, is the caller. calc reads its own
// import beside it: 5 * 100 + 50. A lookup that carried the caller's body
// import into the callee read p's five there too, 5 * 100 + 5 = 505.
TEST(PackageImportSim, CalleeWithoutImportKeepsTheModulesFunctionOverCallers) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  function int plain(); return five(); endfunction\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    return five() * 100 + plain();\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            550u);
}

// §26.3 with §23.9, for a variable: `v` read in plain() is the module's 40,
// the nearest declaration outward from plain's own scope, while `v` in calc,
// whose body imports p, is p's 3: 3 * 100 + 40. A callee reading its caller's
// import would find p's v first, 3 * 100 + 3 = 303.
TEST(PackageImportSim, CalleeWithoutImportKeepsTheModulesVariableOverCallers) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int v = 3;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int v = 40;\n"
                      "  function int plain(); return v; endfunction\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    return v * 100 + plain();\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            340u);
}

// §26.3 with §23.9, for a task enabled from a task: t_plain has no import,
// so its `five()` is the module's 50 whatever body enables it; t_calc's own
// `five()` is p's 5 through its body import. 5 * 100 + 50 is 550 against the
// 505 of a callee reading its enabling task's import.
TEST(PackageImportSim, EnabledTaskWithoutImportKeepsTheModulesFunction) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  task t_plain(output int r); r = five(); endtask\n"
                      "  task t_calc(output int r);\n"
                      "    import p::*;\n"
                      "    int q;\n"
                      "    t_plain(q);\n"
                      "    r = five() * 100 + q;\n"
                      "  endtask\n"
                      "  int out;\n"
                      "  initial t_calc(out);\n"
                      "endmodule\n",
                      "out"),
            550u);
}

// §26.3 with §23.9 and §8.6: a method of a class the module declares is a
// scope nested in the class and then the module, so `five()` in get() is the
// module's 50 although calc(), which imports p in its body, is what calls the
// method: 5 * 100 + 50. A method frame that let the search run on into the
// caller's body read 505.
TEST(PackageImportSim, ClassMethodWithoutImportKeepsTheModulesFunction) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  class C;\n"
                      "    function int get(); return five(); endfunction\n"
                      "  endclass\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    C c = new;\n"
                      "    return five() * 100 + c.get();\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            550u);
}

// §8.7 (printed page 184) with §26.3 (printed 810) and §23.9 (printed 761):
// a property's default is set at construction, and it is an expression of
// the class declaration's scope, nested in the module, so `five()` in C's
// `int x = five()` is the module's 50 whichever body constructs the object:
// calc(), whose body imports p, reads p's 5 for its own call and C's 50
// through the object, 5 * 100 + 50. Defaults evaluated in the constructing
// body's frames read p's five through calc's import for 505.
TEST(PackageImportSim, PropertyDefaultKeepsTheModulesFunctionOverConstructors) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  class C;\n"
                      "    int x = five();\n"
                      "  endclass\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    C c = new;\n"
                      "    return five() * 100 + c.x;\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            550u);
}

// §26.2 with §8.7: a class p declares reads p's names bare in its property
// defaults, so `int x = five()` in p::C is p's 5 when a module body with no
// import of p, and a five() of its own, constructs the object: the body's
// own call is the module's 50, 50 * 100 + 5. A default read in the
// constructing body's scope took the module's five, 50 * 100 + 50 = 5050.
TEST(PackageImportSim,
     PackageClassPropertyDefaultReadsItsPackageFromAModuleBody) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "  class C;\n"
                      "    int x = five();\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  function int calc();\n"
                      "    p::C c = new;\n"
                      "    return five() * 100 + c.x;\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            5005u);
}

// §8.25 with §8.7: the value parameter of the specialization `C#(7)::new`
// is bound for the construction (BindClassParams in eval_function.cpp), so
// `int x = W` reads 7 in a body that imports p, whose own W of 3 never
// stands ahead of the class's parameter: 7 * 100 + 5 from calc's imported
// five(). A defaults frame that hid the binding beneath it read p's 3 for
// 305, or nothing of the 7 at all.
TEST(PackageImportSim,
     SpecializedClassPropertyDefaultReadsItsParameterInAnImportingBody) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int W = 3;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  class C #(int W = 1);\n"
                      "    int x = W;\n"
                      "  endclass\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    C c;\n"
                      "    c = C#(7)::new;\n"
                      "    return c.x * 100 + five();\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            705u);
}

// §26.3 with §23.9: a named begin-end block and a foreach loop inside calc's
// body are scopes nested in the body, not subroutines of their own, so the
// `five()` written in each still reaches the body's import of p: 5 in the
// block and 5 for each of arr's two elements, 15. A search that ended at the
// nearest frame of any kind would fall back to the module's 50 in both, 150.
TEST(PackageImportSim, BlockAndForeachInsideAnImportingBodySeeItsImport) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  int arr[2];\n"
                      "  function int calc();\n"
                      "    import p::*;\n"
                      "    int s;\n"
                      "    s = 0;\n"
                      "    begin : blk\n"
                      "      s = s + five();\n"
                      "    end\n"
                      "    foreach (arr[i]) s = s + five();\n"
                      "    return s;\n"
                      "  endfunction\n"
                      "  int out;\n"
                      "  initial out = calc();\n"
                      "endmodule\n",
                      "out"),
            15u);
}

// §26.3 with §26.2: a package function's body reads its own package's names
// bare, its frame carrying the package (printed pages 808 and 810), so
// p::ten's `five()` is p's 5 doubled even when the call comes from a module
// function plain() that declares no import and stands beside a module five of
// 50: 10 + 50. A package frame that lost its package to the boundary would
// call the module's five in ten, 100 + 50 = 150.
TEST(PackageScopeReferenceSim,
     PackageFunctionCalledFromAModuleBodyStillReadsItsPackage) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  function int five(); return 5; endfunction\n"
                      "  function int ten(); return five() * 2; endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  function int five(); return 50; endfunction\n"
                      "  function int plain(); return p::ten() + five(); "
                      "endfunction\n"
                      "  int out;\n"
                      "  initial out = plain();\n"
                      "endmodule\n",
                      "out"),
            60u);
}

// §26.3 Example 2 (printed page 811), the shape of #3952's second probe: the
// block's `x = 1` finds no candidate in b, whose own `import p2::*` stands
// after it, and is searched outward into top, whose wildcard import of p
// supplies x, so p::x is imported into top and written; the module's own
// read of x after the block is p::x too. The read the block makes after its
// import is searched in b first, where p2's x is now a candidate (printed
// 810), so z is p2's 7 and never p's: 1 * 1000 + 1 * 100 + 7. A block whose
// import bound at module level, behind the module's import of p, read z = 1
// for 1101.
TEST(PackageImportSim, BlockImportAfterTheReferenceLeavesItToTheOuterScope) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int x;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  int x = 7;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p::*;\n"
                      "  int y, z;\n"
                      "  if (1) begin : b\n"
                      "    initial x = 1;\n"
                      "    import p2::*;\n"
                      "    initial #1 z = x;\n"
                      "  end\n"
                      "  initial #2 y = p::x * 1000 + x * 100 + z;\n"
                      "endmodule\n",
                      "y"),
            1107u);
}

// §26.3 with §27.5: an import written in a generate block is the block's, so
// two sibling blocks importing two packages that both declare x each read
// their own, 5 in b and 9 in c, while the module imports nothing that
// supplies the name: 5 * 100 + 9. Both imports recorded as the module's bound
// x to p2's once, and c read 5 for 505.
TEST(PackageImportSim, SiblingBlocksEachReadTheirOwnImport) {
  EXPECT_EQ(RunAndGet("package p2;\n"
                      "  int x = 5;\n"
                      "endpackage\n"
                      "package p3;\n"
                      "  int x = 9;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y, seen_b, seen_c;\n"
                      "  if (1) begin : b\n"
                      "    import p2::*;\n"
                      "    initial seen_b = x;\n"
                      "  end\n"
                      "  if (1) begin : c\n"
                      "    import p3::*;\n"
                      "    initial seen_c = x;\n"
                      "  end\n"
                      "  initial #1 y = seen_b * 100 + seen_c;\n"
                      "endmodule\n",
                      "y"),
            509u);
}

// §26.3 (printed page 810): a reference in block c nested in b is searched in
// c, then in b -- b's declarations first and then the candidates of the
// import b wrote before c -- and only then in top. c's x is therefore p2's 5
// through b's import rather than p's 3 through the module's, and c's k is b's
// own 40 rather than p2's 2, the declaration standing ahead of the candidate:
// 45 * 100 + 40. With b's import bound as the module's behind p's, c read
// x = 3 for 4340.
TEST(PackageImportSim, NestedBlockReachesTheEnclosingBlocksImport) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int x = 3;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  int x = 5;\n"
                      "  int k = 2;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p::*;\n"
                      "  int y, inner, own;\n"
                      "  if (1) begin : b\n"
                      "    import p2::*;\n"
                      "    int k = 40;\n"
                      "    if (1) begin : c\n"
                      "      initial inner = x + k;\n"
                      "    end\n"
                      "    initial own = k;\n"
                      "  end\n"
                      "  initial #1 y = inner * 100 + own;\n"
                      "endmodule\n",
                      "y"),
            4540u);
}

// §26.3 with §27.4: each loop generate block instance is a scope of its own,
// so each instance's import is its own too. The first initial of each
// instance stands before the import and adds p's 1 through the module's
// import, twice for 2, and the second stands after it and adds p2's 10
// through the block's, twice more for 22. Both imports recorded as the
// module's made every add p's for 4.
TEST(PackageImportSim, LoopBlockInstanceImportBindsAfterItsPoint) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  int x = 1;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  int x = 10;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p::*;\n"
                      "  int y;\n"
                      "  genvar g;\n"
                      "  for (g = 0; g < 2; g++) begin : blk\n"
                      "    initial y = y + x;\n"
                      "    import p2::*;\n"
                      "    initial #1 y = y + x;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            22u);
}

// §26.6 (printed pages 815-816): an import of a declaration reached through
// an export is an import of the original, so `import p2::x` and `import
// p4::x`, p2 exporting p1's x by name and p4 by wildcard, both bind the
// module's bare x to p1's one variable and conflict with nothing under
// §26.3 (printed 810). The write of 37 through the bare name lands in p1's x
// and the bare read and the qualified p1::x read it back: 37 * 100 + 37.
// The elaborator reported the second import as conflicting with the first,
// which the fixture refuses; a bare x bound to anything but p1's would read
// 0 beside p1::x's 37, 3700 or 37.
TEST(PackageImportSim, TwoExplicitImportsThroughTwoExportsBindOneVariable) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::x;\n"
                      "  export p1::x;\n"
                      "endpackage\n"
                      "package p4;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p2::x;\n"
                      "  import p4::x;\n"
                      "  int y;\n"
                      "  initial x = 37;\n"
                      "  initial #1 y = x * 100 + p1::x;\n"
                      "endmodule\n",
                      "y"),
            3737u);
}

// §26.6 (printed pages 815-816): an export makes the declaration the package
// imported available through the package, an import of it being an import
// of the original, so `p2::x` after `import p1::x; export p1::x;` is p1's x
// -- the clause's own comment has p1::x and p2::x as one declaration. The
// write of 37 through p2's qualifier is read back through p1's own, through
// p4's, which re-exports p1 by wildcard, and through the bare name `import
// p2::*` binds: 37 * 10000 + 37 * 100 + 37. The write resolved to a "p2.x"
// key no package storage stood under and landed nowhere, every read then
// answering p1's untouched 0.
TEST(PackageImportSim, ReExportedNameThroughTheExportingPackageQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::x;\n"
                      "  export p1::x;\n"
                      "endpackage\n"
                      "package p4;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p2::*;\n"
                      "  int y;\n"
                      "  initial p2::x = 37;\n"
                      "  initial #1 y = p1::x * 10000 + p4::x * 100 + x;\n"
                      "endmodule\n",
                      "y"),
            373737u);
}

// §26.6 with §26.3: a subroutine an export hands on is called through the
// exporting package's qualifier as through the declaring one's, and §13.4
// runs its body in the scope of its declaration, so `p2::f()` is p1's f
// reading p1's k: 4 * 10 + 1. No subroutine stood under "p2::f" before, the
// call answering 0; a registration that lost p1's scope would read no k and
// answer 1.
TEST(PackageImportSim, ReExportedFunctionCalledThroughTheExportingPackage) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int k = 4;\n"
                      "  function automatic int f();\n"
                      "    return k * 10 + 1;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::f;\n"
                      "  export p1::f;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p2::f();\n"
                      "endmodule\n",
                      "y"),
            41u);
}

// §26.6 (printed 815): `export *::*` hands on every declaration the package
// imported, and an export of a re-exported name reaches the original along
// the chain -- p3 exports what it imports from p2, which exports p1's x by
// wildcard -- so the write of 5 through `p3::x` is read through `p2::x` and
// `p1::x`: 5 * 10 + 5. A chain followed one link only would leave "p3.x"
// unbound and both reads at 0.
TEST(PackageImportSim, ReExportChainWrittenThroughTheLastPackage) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "endpackage\n"
                      "package p3;\n"
                      "  import p2::x;\n"
                      "  export *::*;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial p3::x = 5;\n"
                      "  initial #1 y = p2::x * 10 + p1::x;\n"
                      "endmodule\n",
                      "y"),
            55u);
}

// §26.6 with §6.19 and §6.20.1: a wildcard export hands on the package's
// parameters and the members of its enumerations, which are constants of the
// declaring package, so `p2::MID` and `p2::K` after `import p1::*; export
// p1::*;` are p1's 6 and 3: 6 * 10 + 3. Neither had storage under p2's key
// and each read 0.
TEST(PackageImportSim,
     WildcardReExportedLiteralAndParameterThroughTheExporter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  typedef enum {LOW, MID = 6, HIGH} level_t;\n"
                      "  parameter int K = 3;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p2::MID * 10 + p2::K;\n"
                      "endmodule\n",
                      "y"),
            63u);
}

// §26.6 (printed pages 815-816) with §26.3: a class an export hands on is
// reached through the exporting package's qualifier as through the declaring
// one's, an import of it being an import of the original, so `p2::C::get()`
// and a handle declared `p2::C h` after `import p1::C; export p1::C;` name
// p1's C: 7 * 100 + 3 from the static method and the default of v. No class
// stood under "p2::C" before, the call answering 0 and the whole reading 3
// at most.
TEST(PackageImportSim, ReExportedClassThroughTheExportingPackageQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    static function int get(); return 7; endfunction\n"
                      "    int v = 3;\n"
                      "  endclass\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::C;\n"
                      "  export p1::C;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p2::C h = new;\n"
                      "    y = p2::C::get() * 100 + h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            703u);
}

// §26.6 (printed 815): `export p1::*` hands on the class the package
// wildcard-imported, and an export of a re-exported class reaches the
// original along the chain -- p3 exports the C it imports from p2 -- so
// `p2::C::get()` and `p3::C::get()` are both p1's 7: 7 * 10 + 7. Neither key
// held a class before and each call answered 0.
TEST(PackageImportSim, ReExportedClassAlongAWildcardExportChain) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    static function int get(); return 7; endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "endpackage\n"
                      "package p3;\n"
                      "  import p2::C;\n"
                      "  export p2::C;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = p2::C::get() * 10 + p3::C::get();\n"
                      "endmodule\n",
                      "y"),
            77u);
}

// §26.6 with §26.3: a module's `import p2::*` brings in the class p2 hands
// on from p1 under its bare name, the import path lowering p1's C as it
// follows the export (LowerAllImported in lowerer_import.cpp), so `C h =
// new` and `C::get()` are p1's: 3 * 100 + 7. Pinned beside the qualified
// forms, which the same lowering now binds under p2's key.
TEST(PackageImportSim, ReExportedClassReachedBareThroughAWildcardImport) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    static function int get(); return 7; endfunction\n"
                      "    int v = 3;\n"
                      "  endclass\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::*;\n"
                      "  export p1::*;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p2::*;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    C h = new;\n"
                      "    y = h.v * 100 + C::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            307u);
}

// §26.6 (printed pages 815-816) with §8.7: a package's class-handle variable
// an export hands on is constructed through the exporting package's
// qualifier as through the declaring one's, `p2::h = new` after `import
// p1::h; export p1::h;` building an object of p1's C into p1's h, so the
// property written through p2 reads back through p1 and p2 alike: 5 * 10 +
// 5. The exporter's key was bound to the storage alone, with no class
// recorded under it, so the `new` had no class to construct, the handle
// stayed null and both reads answered 0.
TEST(PackageImportSim, ReExportedClassHandleConstructedThroughTheExporter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
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
                      "    p2::h.v = 5;\n"
                      "    y = p1::h.v * 10 + p2::h.v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            55u);
}

// §26.6 (printed 815) with §6.16: a package's string variable an export hands
// on takes a whole string through the exporting package's qualifier and
// answers its methods there, `p2::s = "abcd"` and `p2::s.len()` after
// `import p1::s; export p1::s;` being p1's s: 4 * 10 + 4 read through p2 and
// p1. Pinned: the string kind travels on the Variable the exporter's key is
// bound to (ShapePackageVariable in lowerer_register.cpp), so a write sized
// to the variable, which would keep four characters of a longer string, and a
// method call answering nothing are both ruled out by the read.
TEST(PackageImportSim, ReExportedStringWrittenAndReadThroughTheExporter) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  string s;\n"
                      "endpackage\n"
                      "package p2;\n"
                      "  import p1::s;\n"
                      "  export p1::s;\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p2::s = \"abcd\";\n"
                      "    y = p2::s.len() * 10 + p1::s.len();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            44u);
}

// §26.2 (printed page 808) lets a package's items reference what the package
// itself declares, and §13.4 runs a function's body in the scope declaring
// it, so the bare `q` and `m` inside p1::add are p1's queue and associative
// array, the ones `p1::q` and `p1::m` reach through §26.3's scope resolution
// operator: one push and one element write, then 1 * 10 + 5. Under the
// defect the body's `q` and `m` found no object: FindQueue and
// FindAssocArray searched the frames, the running instance's key and the
// bare key and never the package frame's "p1.q" and "p1.m", so the
// push_back ran on no queue and the element write fell to the carrier
// variable, and the read through the qualifier afterwards saw an empty queue
// and an element never written -- 0. A queue found and an associative array
// missed would read 10, the other way round 5.
TEST(PackageImportSim,
     PackageFunctionWritesItsOwnQueueAndAssociativeArrayBare) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int q[$];\n"
                      "  int m[string];\n"
                      "  function void add(int v);\n"
                      "    q.push_back(v);\n"
                      "    m[\"k\"] = v;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::add(5);\n"
                      "    y = p1::q.size() * 10 + p1::m[\"k\"];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            15u);
}

// §26.3 (printed page 809): a wildcard import makes another package's
// declarations visible in the importing package without a qualifier, so the
// bare `r` inside p1::addr is p0's queue, the object `p0::r` reaches. Two
// calls push 3 and then 4, so the size is 2 and the element at 1 is 4:
// 2 * 10 + 4. The same defect left the body's `r` reaching no queue, "p0.r"
// being a key of p1's import that the lookup never tried, and the read
// through p0's qualifier afterwards saw an empty queue -- 0. A lookup that
// tried p1's own key alone and not its import's would read 0 as well, which
// is what distinguishes this case from the one above.
TEST(PackageImportSim, PackageFunctionWritesAnImportedPackagesQueueBare) {
  EXPECT_EQ(RunAndGet("package p0;\n"
                      "  int r[$];\n"
                      "endpackage\n"
                      "package p1;\n"
                      "  import p0::*;\n"
                      "  function void addr(int v);\n"
                      "    r.push_back(v);\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::addr(3);\n"
                      "    p1::addr(4);\n"
                      "    y = p0::r.size() * 10 + p0::r[1];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            24u);
}

}  // namespace
