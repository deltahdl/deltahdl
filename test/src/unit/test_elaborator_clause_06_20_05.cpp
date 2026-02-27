// §6.20.5: Specify parameters


#include "common/types.h"
#include "elaboration/sensitivity.h"
#include "elaboration/type_eval.h"
#include "lexer/token.h"

#include "fixture_elaborator.h"

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
