#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(ConstConstantElaboration, ConstWithoutInitializerIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstIntWithInitializerSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  const int x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstReassignmentIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x = 5;\n"
      "  initial x = 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstRealWithInitializerSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  const real PI = 3.14159;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstStringWithInitializerSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  const string LABEL = \"test\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstNonblockingReassignmentIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x = 5;\n"
      "  initial x <= 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstInitializedFromParameterSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top #(parameter P = 5);\n"
      "  const int x = P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstInitializedFromLocalparamSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  localparam LP = 10;\n"
      "  const int x = LP;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstInitializedFromAnotherConstSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  const int a = 5;\n"
      "  const int b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstCreatesVariable) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  const int LIMIT = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "LIMIT") {
      found = true;
      EXPECT_NE(v.init_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
