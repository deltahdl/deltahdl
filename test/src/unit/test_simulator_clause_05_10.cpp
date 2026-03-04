#include <cstring>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

TEST(SimCh510, StructLitPositional) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{8'hAA, 8'hBB};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0xAABBu);
}

TEST(SimCh510, StructLitMemberName) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{a: 8'h11, b: 8'h22};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x1122u);
}

TEST(SimCh510, StructLitDefault) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{default: 8'hFF};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0xFFFFu);
}

TEST(SimCh510, StructLitMemberNameReverse) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{b: 8'h22, a: 8'h11};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x1122u);
}

TEST(SimCh510, StructLitVarInit) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } pt_t;\n"
      "  pt_t p = '{x: 8'hAA, y: 8'hBB};\n"
      "endmodule\n",
      "p");
  EXPECT_EQ(v, 0xAABBu);
}

TEST(SimCh510, StructLitDefaultDiffWidth) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [3:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{default: '1};\n"
      "endmodule\n",
      "c");

  EXPECT_EQ(v, 0xFFFu);
}

TEST(SimCh510, StructLitPositionalThree) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] a; logic [7:0] b; logic [7:0] c;\n"
      "  } abc_t;\n"
      "  abc_t s;\n"
      "  initial s = '{8'h11, 8'h22, 8'h33};\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(v, 0x112233u);
}

TEST(SimCh510, StructLitFieldAccess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } pt_t;\n"
      "  pt_t p;\n"
      "  logic [7:0] rx, ry;\n"
      "  initial begin\n"
      "    p = '{x: 8'hDE, y: 8'hAD};\n"
      "    rx = p.x;\n"
      "    ry = p.y;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(design, nullptr);
  if (!design) return;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vrx = f.ctx.FindVariable("rx");
  auto* vry = f.ctx.FindVariable("ry");
  EXPECT_NE(vrx, nullptr);
  EXPECT_NE(vry, nullptr);
  if (!vrx || !vry) return;
  EXPECT_EQ(vrx->value.ToUint64(), 0xDEu);
  EXPECT_EQ(vry->value.ToUint64(), 0xADu);
}

TEST(SimCh510, StructLitDefaultZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{default: 0};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0u);
}

TEST(SimCh510, StructLitPositionalInit) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c = '{8'h55, 8'hAA};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x55AAu);
}
