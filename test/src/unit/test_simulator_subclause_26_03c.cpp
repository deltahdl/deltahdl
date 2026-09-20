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

}  // namespace
