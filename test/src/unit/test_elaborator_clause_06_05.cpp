// §6.5: for more details.


#include "common/types.h"
#include "elaboration/sensitivity.h"
#include "elaboration/type_eval.h"
#include "lexer/token.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- §6.5: Variable constraints ---
TEST(Elaboration, VarRedeclare_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  reg v;\n"
      "  wire v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, VarMixedAssign_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  wire clk = 0;\n"
      "  int v;\n"
      "  assign v = 12;\n"
      "  always @(posedge clk) v <= ~v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
