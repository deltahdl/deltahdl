#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(AssignmentExtensionTruncation, ContAssignInfersLhsWidthWhenWiderThanRhs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [15:0] wide;\n"
      "  logic [3:0] narrow;\n"
      "  assign wide = narrow;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->assigns.size(), 1);
  EXPECT_EQ(mod->assigns[0].width, 16);
}

TEST(AssignmentExtensionTruncation,
     ContAssignInfersLhsWidthWhenNarrowerThanRhs) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [3:0] narrow;\n"
      "  logic [15:0] wide;\n"
      "  assign narrow = wide;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->assigns.size(), 1);
  EXPECT_EQ(mod->assigns[0].width, 4);
}

}  // namespace
