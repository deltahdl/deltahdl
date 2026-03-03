// §10.7: Assignment extension and truncation

#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

// --- Width inference tests ---
TEST(Elaboration, WidthInference_ContAssignWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [7:0] a, b;\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->assigns.size(), 1);
  EXPECT_EQ(mod->assigns[0].width, 8);
}

// ---------------------------------------------------------------------------
// 25. Blocking assignment preserving width/truncation.
// ---------------------------------------------------------------------------
TEST(SimCh10, BlockingAssignTruncation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  initial begin\n"
      "    narrow = 8'hFF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("narrow");
  ASSERT_NE(var, nullptr);
  // 8'hFF truncated to 4 bits = 0xF.
  EXPECT_EQ(var->value.width, 4u);
  EXPECT_EQ(var->value.ToUint64(), 0xFu);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with different widths — zero extension.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAWidthExtension) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] wide;\n"
      "  initial begin\n"
      "    wide <= 8'hFF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("wide");
  ASSERT_NE(var, nullptr);
  // 8'hFF zero-extended to 32 bits = 0x000000FF.
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
  EXPECT_EQ(var->value.width, 32u);
}

}  // namespace
