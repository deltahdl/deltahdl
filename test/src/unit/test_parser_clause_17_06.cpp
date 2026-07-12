#include "fixture_parser.h"

using namespace delta;

namespace {

// §17.6: one or more covergroup declarations are permitted within a checker.
// The clause's my_check shape writes the covergroup directly in the checker
// body (built from real §19.3 covergroup syntax), and it parses cleanly. This
// is the accepting baseline the placement prohibition is contrasted against.
TEST(CovergroupInCheckerPlacement, CovergroupInCheckerBodyParses) {
  EXPECT_TRUE(
      ParseOk("checker chk(logic clk, logic active);\n"
              "  covergroup cg_active @(posedge clk);\n"
              "    cp_active : coverpoint active;\n"
              "  endgroup\n"
              "endchecker\n"));
}

// §17.6 (negative form): a covergroup declaration shall not appear in any
// procedural block of the checker. Relocating the very same covergroup into an
// always_ff procedure is illegal — a covergroup declaration is not a procedural
// statement, so the parser rejects the checker. Only the placement changed
// relative to the accepting baseline above.
TEST(CovergroupInCheckerPlacement, CovergroupInsideProceduralBlockIsRejected) {
  EXPECT_FALSE(
      ParseOk("checker chk(logic clk, logic active);\n"
              "  always_ff @(posedge clk) begin\n"
              "    covergroup cg_active @(posedge clk);\n"
              "      cp_active : coverpoint active;\n"
              "    endgroup\n"
              "  end\n"
              "endchecker\n"));
}

}  // namespace
