// §6.14: Chandle data type


#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- §6.14 Chandle restriction tests ---
TEST(Elaboration, ChandlePort_Error) {
  // §6.14: chandle cannot be used as a port.
  ElabFixture f;
  ElaborateSrc(
      "module top(input chandle ch);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, ChandleContAssign_Error) {
  // §6.14: chandle cannot be used in continuous assignment.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, ChandleSensitivity_Error) {
  // §6.14: chandle cannot appear in event expression.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle ch;\n"
      "  always @(ch) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, ChandleVarDecl_OK) {
  // §6.14: chandle variable declaration is legal.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle ch;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
