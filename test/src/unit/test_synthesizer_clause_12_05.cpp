// §12.5: Case statement

#include <gtest/gtest.h>

#include "synthesis/aig.h"
#include "synthesis/synth_lower.h"
#include "fixture_synthesizer.h"

using namespace delta;

namespace {

TEST(SynthLower, AlwaysCombCaseStmt) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f,
                   "module m(input logic [1:0] sel, output logic [1:0] y);\n"
                   "  always_comb begin\n"
                   "    case (sel)\n"
                   "      2'b00: y = 2'b01;\n"
                   "      2'b01: y = 2'b10;\n"
                   "      default: y = 2'b00;\n"
                   "    endcase\n"
                   "  end\n"
                   "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->inputs.size(), 2);
  EXPECT_EQ(aig->outputs.size(), 2);
}

}  // namespace
