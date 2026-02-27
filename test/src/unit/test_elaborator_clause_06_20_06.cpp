// §6.20.6: Const constants


#include "common/types.h"
#include "elaboration/sensitivity.h"
#include "elaboration/type_eval.h"
#include "lexer/token.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// --- §6.20.6: Const constants ---
TEST(Elaboration, ConstVarNoInit_Error) {
  // const variable without initializer is an error.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, ConstVarWithInit_OK) {
  // const variable with initializer is fine.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  const int x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, ConstVarReassign_Error) {
  // Assignment to const variable is an error.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x = 5;\n"
      "  initial x = 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
