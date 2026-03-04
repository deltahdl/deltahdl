#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

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

  EXPECT_EQ(var->value.width, 4u);
  EXPECT_EQ(var->value.ToUint64(), 0xFu);
}

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

  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
  EXPECT_EQ(var->value.width, 32u);
}

TEST(SimCh10b, NBAPreservesWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a <= 16'hCAFE;\n"
      "    b <= 8'hBE;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.width, 16u);
  EXPECT_EQ(a->value.ToUint64(), 0xCAFEu);
  EXPECT_EQ(b->value.width, 8u);
  EXPECT_EQ(b->value.ToUint64(), 0xBEu);
}

}
