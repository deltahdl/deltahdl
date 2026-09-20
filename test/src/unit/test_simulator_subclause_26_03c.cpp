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

}  // namespace
