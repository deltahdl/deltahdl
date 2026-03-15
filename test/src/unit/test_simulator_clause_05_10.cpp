#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LexicalConventionSim, PositionalTwoFields) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{8'hAA, 8'hBB};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0xAABBu);
}

TEST(LexicalConventionSim, PositionalThreeFields) {
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

TEST(LexicalConventionSim, MemberNameAndValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{a: 8'h11, b: 8'h22};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x1122u);
}

TEST(LexicalConventionSim, MemberNameReverseOrder) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{b: 8'h22, a: 8'h11};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x1122u);
}

TEST(LexicalConventionSim, DefaultAllOnes) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{default: 8'hFF};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0xFFFFu);
}

TEST(LexicalConventionSim, DefaultZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{default: 0};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0u);
}

TEST(LexicalConventionSim, DefaultDifferentFieldWidths) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [3:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{default: '1};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0xFFFu);
}

TEST(LexicalConventionSim, VarInitPositional) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c = '{8'h55, 8'hAA};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x55AAu);
}

TEST(LexicalConventionSim, VarInitNamed) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } pt_t;\n"
      "  pt_t p = '{x: 8'hAA, y: 8'hBB};\n"
      "endmodule\n",
      "p");
  EXPECT_EQ(v, 0xAABBu);
}

TEST(LexicalConventionSim, FieldAccessAfterAssign) {
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

TEST(LexicalConventionSim, TypePrefixedStructLiteral) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = ab_t'{8'hDE, 8'hAD};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0xDEADu);
}

TEST(LexicalConventionSim, ReplicationStructLiteral) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] x; logic [7:0] y; logic [7:0] z;\n"
      "  } xyz_t;\n"
      "  xyz_t s;\n"
      "  initial s = '{3{8'hAA}};\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(v, 0xAAAAAAu);
}

TEST(LexicalConventionSim, NestedBracesArrayOfStructs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t arr [0:1];\n"
      "  logic [15:0] r0, r1;\n"
      "  initial begin\n"
      "    arr = '{'{8'h11, 8'h22}, '{8'h33, 8'h44}};\n"
      "    r0 = arr[0];\n"
      "    r1 = arr[1];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(design, nullptr);
  if (!design) return;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* vr0 = f.ctx.FindVariable("r0");
  auto* vr1 = f.ctx.FindVariable("r1");
  EXPECT_NE(vr0, nullptr);
  EXPECT_NE(vr1, nullptr);
  if (!vr0 || !vr1) return;
  EXPECT_EQ(vr0->value.ToUint64(), 0x1122u);
  EXPECT_EQ(vr1->value.ToUint64(), 0x3344u);
}

}  // namespace
