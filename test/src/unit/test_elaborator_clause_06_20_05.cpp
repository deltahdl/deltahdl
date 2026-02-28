// §6.20.5: Specify parameters

#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

// --- §6.20.5: Specparam restriction ---
TEST(Elaboration, SpecparamInParam_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  specparam delay = 50;\n"
      "  parameter p = delay + 2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
