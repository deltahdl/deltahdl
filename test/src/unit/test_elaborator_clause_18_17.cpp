// §18.17: Random sequence generation—randsequence

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Randsequence with if-else, repeat, case elaborates
TEST(ElabA612, ControlFlowProdsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : if (1) a else b;\n"
      "      a : repeat(3) c;\n"
      "      b : case (0) 0: c; default: c; endcase;\n"
      "      c : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — Elaboration
// =============================================================================
// Basic randsequence elaborates without errors
TEST(ElabA612, BasicRandsequenceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : first second;\n"
      "      first : { ; };\n"
      "      second : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
