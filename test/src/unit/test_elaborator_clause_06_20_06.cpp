#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(Elaboration, ConstVarNoInit_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, ConstVarWithInit_OK) {
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
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x = 5;\n"
      "  initial x = 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, ConstRealWithInit_OK) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  const real PI = 3.14159;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, ConstStringWithInit_OK) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  const string LABEL = \"test\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
