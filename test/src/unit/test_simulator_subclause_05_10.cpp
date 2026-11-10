#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(StructLiteralSim, PositionalTwoFields) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{8'hAA, 8'hBB};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0xAABBu);
}

TEST(StructLiteralSim, PositionalThreeFields) {
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

TEST(StructLiteralSim, MemberNameAndValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{a: 8'h11, b: 8'h22};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x1122u);
}

TEST(StructLiteralSim, MemberNameReverseOrder) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{b: 8'h22, a: 8'h11};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x1122u);
}

TEST(StructLiteralSim, DefaultAllOnes) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{default: 8'hFF};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0xFFFFu);
}

TEST(StructLiteralSim, DefaultZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{default: 0};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0u);
}

TEST(StructLiteralSim, DefaultDifferentFieldWidths) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [3:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = '{default: '1};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0xFFFu);
}

TEST(StructLiteralSim, VarInitPositional) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c = '{8'h55, 8'hAA};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x55AAu);
}

TEST(StructLiteralSim, VarInitNamed) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] x; logic [7:0] y; } pt_t;\n"
      "  pt_t p = '{x: 8'hAA, y: 8'hBB};\n"
      "endmodule\n",
      "p");
  EXPECT_EQ(v, 0xAABBu);
}

TEST(StructLiteralSim, FieldAccessAfterAssign) {
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

TEST(StructLiteralSim, TypePrefixedStructLiteral) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t c;\n"
      "  initial c = ab_t'{8'hDE, 8'hAD};\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0xDEADu);
}

TEST(StructLiteralSim, ReplicationStructLiteral) {
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

TEST(StructLiteralSim, NestedBracesArrayOfStructs) {
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

TEST(StructLiteralSim, TypedByFunctionReturnContext) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  function ab_t make();\n"
      "    return '{8'hDE, 8'hAD};\n"
      "  endfunction\n"
      "  logic [15:0] r;\n"
      "  initial r = make();\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0xDEADu);
}

TEST(StructLiteralSim, PositionalLiteralFillsARealMember) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef struct { int a; real b; } ab;\n"
      "  ab s = '{8'hA5, 2.5};\n"
      "  initial $display(\"s.a=%0d s.b=%g\", s.a, s.b);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "s.a=165 s.b=2.5\n");
}

TEST(StructLiteralSim, TypeKeysFillTheMembersOfTheirType) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef struct { int a; shortreal b; } ab;\n"
      "  typedef struct { int a; logic [7:0] c; int e; real r; } s_t;\n"
      "  ab d;\n"
      "  s_t s;\n"
      "  initial begin\n"
      "    d = ab'{int: 3, shortreal: 1.5};\n"
      "    s = '{int: 5, default: 1};\n"
      "    $display(\"%0d %g %0d %0d %0d %g\", d.a, d.b, s.a, s.c, s.e, s.r);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 1.5 5 1 5 1\n");
}

TEST(StructLiteralSim, NamedLiteralFillsARealMember) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef struct { int a; real b; } ab;\n"
      "  ab s = '{b: 1.25, a: 7};\n"
      "  initial $display(\"s.a=%0d s.b=%g\", s.a, s.b);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "s.a=7 s.b=1.25\n");
}

TEST(StructLiteralSim, PositionalLiteralPlacesAMemberAfterAReal) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef struct { real b; int a; } ba;\n"
      "  ba s = '{2.5, 165};\n"
      "  initial $display(\"s.a=%0d s.b=%g\", s.a, s.b);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "s.a=165 s.b=2.5\n");
}

TEST(StructLiteralSim, RealMemberReadsAsAReal) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef struct { int a; real b; } ab;\n"
      "  ab s = '{1, 2.5};\n"
      "  real r;\n"
      "  initial begin\n"
      "    r = s.b;\n"
      "    $display(\"%g\", r + 1.0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3.5\n");
}

TEST(StructLiteralSim, ReplicatedPatternFillsEachMember) {
  SimFixture f;
  auto* s = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { byte x, y, z; } s_t;\n"
      "  s_t s = '{3{1}};\n"
      "  s_t p;\n"
      "  initial p = '{3{2}};\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->value.ToUint64(), 0x010101u);
  EXPECT_EQ(f.ctx.FindVariable("p")->value.ToUint64(), 0x020202u);
}

TEST(StructLiteralSim, NestedReplicationFillsAnArrayOfStructures) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {int a, b[4];} ab_t;\n"
      "  int a, b, c;\n"
      "  ab_t e;\n"
      "  ab_t v1[1:0] [2:0];\n"
      "  ab_t w1[1:0] [2:0] = '{2{'{3{'{8,'{2{1,2}}}}}}};\n"
      "  initial begin\n"
      "    a = 5; b = 6; c = 7;\n"
      "    v1 = '{2{'{3{'{a,'{2{b,c}}}}}}};\n"
      "    for (int i = 0; i < 2; i++)\n"
      "      for (int j = 0; j < 3; j++) begin\n"
      "        e = v1[i][j];\n"
      "        $write(\"%0d:%0d%0d%0d%0d \", e.a, e.b[0], e.b[1], e.b[2],\n"
      "               e.b[3]);\n"
      "      end\n"
      "    $display(\"\");\n"
      "    for (int i = 0; i < 2; i++)\n"
      "      for (int j = 0; j < 3; j++) begin\n"
      "        e = w1[i][j];\n"
      "        $write(\"%0d:%0d%0d%0d%0d \", e.a, e.b[0], e.b[1], e.b[2],\n"
      "               e.b[3]);\n"
      "      end\n"
      "    $display(\"\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "5:6767 5:6767 5:6767 5:6767 5:6767 5:6767 \n"
            "8:1212 8:1212 8:1212 8:1212 8:1212 8:1212 \n");
}

TEST(StructLiteralSim, NestedBracesFillNarrowMembersOfAMultidimensionalArray) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {byte x; shortint y;} s_t;\n"
      "  s_t e;\n"
      "  s_t m[0:1] [0:1];\n"
      "  s_t d[0:1] [0:1] = '{'{'{1, 2}, '{3, 4}}, '{'{5, 6}, '{7, 8}}};\n"
      "  initial begin\n"
      "    m = '{'{'{1, 2}, '{3, 4}}, '{'{5, 6}, '{7, 8}}};\n"
      "    for (int i = 0; i < 2; i++)\n"
      "      for (int j = 0; j < 2; j++) begin\n"
      "        e = m[i][j];\n"
      "        $write(\"%0d,%0d \", e.x, e.y);\n"
      "      end\n"
      "    $display(\"\");\n"
      "    for (int i = 0; i < 2; i++)\n"
      "      for (int j = 0; j < 2; j++) begin\n"
      "        e = d[i][j];\n"
      "        $write(\"%0d,%0d \", e.x, e.y);\n"
      "      end\n"
      "    $display(\"\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1,2 3,4 5,6 7,8 \n1,2 3,4 5,6 7,8 \n");
}

TEST(StructLiteralSim, ReplicationFillsAnArrayMember) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {int a, b[4];} ab_t;\n"
      "  ab_t r = '{1, '{2{3, 4}}};\n"
      "  ab_t p, w;\n"
      "  initial begin\n"
      "    p = '{1, '{2{3, 4}}};\n"
      "    w = '{1, '{3, 4, 3, 4}};\n"
      "    $display(\"%0d:%0d%0d%0d%0d %0d:%0d%0d%0d%0d %0d:%0d%0d%0d%0d\",\n"
      "             r.a, r.b[0], r.b[1], r.b[2], r.b[3], p.a, p.b[0],\n"
      "             p.b[1], p.b[2], p.b[3], w.a, w.b[0], w.b[1], w.b[2],\n"
      "             w.b[3]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1:3434 1:3434 1:3434\n");
}

}  // namespace
