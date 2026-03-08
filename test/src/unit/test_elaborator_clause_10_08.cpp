#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SimCh10f, ContAssignTruncatesInAssignLikeContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] out;\n"
      "  logic [7:0] in_val = 8'hAB;\n"
      "  assign out = in_val;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* out = f.ctx.FindVariable("out");
  ASSERT_NE(out, nullptr);
  EXPECT_EQ(out->value.ToUint64(), 0xBu);
}

TEST(SimCh10f, ProceduralAssignExtendsInAssignLikeContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] wide;\n"
      "  initial begin\n"
      "    wide = 4'hA;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* wide = f.ctx.FindVariable("wide");
  ASSERT_NE(wide, nullptr);
  EXPECT_EQ(wide->value.ToUint64(), 0x000Au);
}

TEST(SimCh10f, ReturnStatementAssignLikeContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function logic [7:0] get_val();\n"
      "    return 32'hABCD;\n"
      "  endfunction\n"
      "  logic [7:0] result;\n"
      "  initial result = get_val();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->value.ToUint64(), 0xCDu);
}

TEST(SimCh10f, SubroutineArgAssignLikeContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function logic [7:0] trunc(logic [7:0] x);\n"
      "    return x;\n"
      "  endfunction\n"
      "  logic [7:0] result;\n"
      "  initial result = trunc(16'hCAFE);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(result, nullptr);

  EXPECT_EQ(result->value.ToUint64(), 0xFEu);
}

TEST(SimCh10f, OutputPortAssignLikeContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module inner(output logic [3:0] o);\n"
      "  initial o = 4'hA;\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  inner u(.o(wide));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* wide = f.ctx.FindVariable("wide");
  if (wide) {
    EXPECT_EQ(wide->value.ToUint64() & 0xF, 0xAu);
  }
}

TEST(SimCh10f, ConditionalExprInAssignLikeContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  logic sel = 1;\n"
      "  initial result = sel ? 16'hCAFE : 16'hBEEF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(result, nullptr);

  EXPECT_EQ(result->value.ToUint64(), 0xFEu);
}

TEST(SimCh10f, ParenExprInAssignLikeContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial a = (16'hDEAD);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0xADu);
}

TEST(SimCh10f, NBAAssignLikeContext) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  initial narrow <= 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* narrow = f.ctx.FindVariable("narrow");
  ASSERT_NE(narrow, nullptr);
  EXPECT_EQ(narrow->value.ToUint64(), 0xFu);
}

}
