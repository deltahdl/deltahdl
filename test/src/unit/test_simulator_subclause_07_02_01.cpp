#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(PackedStructSimulation, MsbFirstBitOrdering_ThreeFields) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] a;\n"
      "    logic [7:0] b;\n"
      "    logic [7:0] c;\n"
      "  } tri_t;\n"
      "  tri_t s;\n"
      "  logic [7:0] ra, rb, rc;\n"
      "  initial begin\n"
      "    s = 24'hAA_BB_CC;\n"
      "    ra = s.a;\n"
      "    rb = s.b;\n"
      "    rc = s.c;\n"
      "  end\n"
      "endmodule\n",
      "ra");
  EXPECT_EQ(v, 0xAAu);
}

TEST(PackedStructSimulation, MsbFirstBitOrdering_MiddleField) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] a;\n"
      "    logic [7:0] b;\n"
      "    logic [7:0] c;\n"
      "  } tri_t;\n"
      "  tri_t s;\n"
      "  logic [7:0] rb;\n"
      "  initial begin s = 24'hAA_BB_CC; rb = s.b; end\n"
      "endmodule\n",
      "rb");
  EXPECT_EQ(v, 0xBBu);
}

TEST(PackedStructSimulation, MsbFirstBitOrdering_LeastSignificantField) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] a;\n"
      "    logic [7:0] b;\n"
      "    logic [7:0] c;\n"
      "  } tri_t;\n"
      "  tri_t s;\n"
      "  logic [7:0] rc;\n"
      "  initial begin s = 24'hAA_BB_CC; rc = s.c; end\n"
      "endmodule\n",
      "rc");
  EXPECT_EQ(v, 0xCCu);
}

TEST(PackedStructSimulation, ArithmeticAdditionOnPackedStruct) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t a, b;\n"
      "  logic [15:0] z;\n"
      "  initial begin\n"
      "    a = 16'h0102;\n"
      "    b = 16'h0304;\n"
      "    z = a + b;\n"
      "  end\n"
      "endmodule\n",
      "z");
  EXPECT_EQ(v, 0x0406u);
}

TEST(PackedStructSimulation, BitwiseAndOnPackedStruct) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } w_t;\n"
      "  w_t x, y;\n"
      "  logic [15:0] z;\n"
      "  initial begin\n"
      "    x = 16'hFF0F;\n"
      "    y = 16'h0F0F;\n"
      "    z = x & y;\n"
      "  end\n"
      "endmodule\n",
      "z");
  EXPECT_EQ(v, 0x0F0Fu);
}

TEST(PackedStructSimulation, AssignFromConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t w;\n"
      "  logic [7:0] rhi;\n"
      "  initial begin w = {8'hAB, 8'hCD}; rhi = w.hi; end\n"
      "endmodule\n",
      "rhi");
  EXPECT_EQ(v, 0xABu);
}

TEST(PackedStructSimulation, PartSelectOnPackedStruct) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t w;\n"
      "  logic [7:0] top_byte;\n"
      "  initial begin w = 16'hABCD; top_byte = w[15:8]; end\n"
      "endmodule\n",
      "top_byte");
  EXPECT_EQ(v, 0xABu);
}

TEST(PackedStructSimulation, SingleBitSelectOnPackedStruct) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t w;\n"
      "  logic msb;\n"
      "  initial begin w = 16'h8000; msb = w[15]; end\n"
      "endmodule\n",
      "msb");
  EXPECT_EQ(v, 1u);
}

TEST(PackedStructSimulation, WriteTwoStateValueToBitMember_OverwritesPriorX) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { bit [7:0] b; logic [7:0] l; } mixed_t;\n"
      "  mixed_t s;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    s = 16'bxxxxxxxx_00000000;\n"
      "    s.b = 8'hA5;\n"
      "    r = s.b;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0xA5u);
}

TEST(PackedStructSimulation, BitMemberInFourStateStruct_ReadsAsTwoState) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { bit [7:0] b; logic [7:0] l; } mixed_t;\n"
      "  mixed_t s;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    s = 16'bxxxxxxxx_00000000;\n"
      "    r = s.b;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0u);
}

TEST(PackedStructSimulation, SignedPackedStructWholeReadSignExtends) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed signed { logic [7:0] a; } b_t;\n"
      "  b_t s;\n"
      "  logic [15:0] r;\n"
      "  initial begin s = 8'hFF; r = s; end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0xFFFFu);
}

TEST(PackedStructSimulation, UnsignedDefaultPackedStructWholeReadZeroExtends) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; } b_t;\n"
      "  b_t s;\n"
      "  logic [15:0] r;\n"
      "  initial begin s = 8'hFF; r = s; end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0x00FFu);
}

TEST(PackedStructSimulation, IntegerTypeMembersPackMsbFirst) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { int a; byte b; } m_t;\n"
      "  m_t m;\n"
      "  logic [31:0] ra;\n"
      "  initial begin m = 40'h1122334455; ra = m.a; end\n"
      "endmodule\n",
      "ra");
  EXPECT_EQ(v, 0x11223344u);
}

TEST(PackedStructSimulation, IndexedPartSelectOnPackedStruct) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t w;\n"
      "  logic [7:0] top_byte;\n"
      "  initial begin w = 16'hABCD; top_byte = w[8+:8]; end\n"
      "endmodule\n",
      "top_byte");
  EXPECT_EQ(v, 0xABu);
}

TEST(PackedStructSimulation, MemberWriteUpdatesWholeVector) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t w;\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    w = 16'h0000;\n"
      "    w.hi = 8'hAB;\n"
      "    result = w;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xAB00u);
}

TEST(PackedStructSimulation, NonblockingWriteToBitMemberReachesThatMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { bit [7:0] b; logic [7:0] l; } mixed_t;\n"
      "  mixed_t s;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    s = 16'h0000;\n"
      "    s.b <= 8'hA5;\n"
      "    #1 r = s.b;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  LowerRunAndCheck(f, design, {{"r", 0xA5u}, {"s", 0xA500u}});
}

TEST(PackedStructSimulation, MemberWriteThroughAClassPropertyLandsInTheValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] b; logic [7:0] l; } pair_t;\n"
      "  class C;\n"
      "    pair_t p;\n"
      "  endclass\n"
      "  logic [15:0] r1;\n"
      "  logic [7:0] r2;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    c.p = 16'hAABB;\n"
      "    c.p.b = 8'h05;\n"
      "    r1 = c.p;\n"
      "    r2 = c.p.b;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  LowerRunAndCheck(f, design, {{"r1", 0x05BBu}, {"r2", 0x05u}});
}

TEST(PackedStructSimulation, MemberReadThroughAClassPropertyTakesItsBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] b; logic [7:0] l; } pair_t;\n"
      "  class C;\n"
      "    pair_t p;\n"
      "  endclass\n"
      "  logic [7:0] rb, rl;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    c.p = 16'hAABB;\n"
      "    rb = c.p.b;\n"
      "    rl = c.p.l;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  LowerRunAndCheck(f, design, {{"rb", 0xAAu}, {"rl", 0xBBu}});
}

TEST(PackedStructSimulation, MemberWriteThroughAPropertyLeavesTheOtherMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] b; logic [7:0] l; } pair_t;\n"
      "  class C;\n"
      "    pair_t p;\n"
      "  endclass\n"
      "  logic [15:0] r1;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    c.p = 16'hAABB;\n"
      "    c.p.l = 8'h07;\n"
      "    r1 = c.p;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  LowerRunAndCheck(f, design, {{"r1", 0xAA07u}});
}

TEST(PackedStructSimulation, ChildInstanceMemberWriteLandsInItsWindow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  typedef struct packed { logic [7:0] opcode; logic [23:0] imm; } "
      "instruction_t;\n"
      "  instruction_t s;\n"
      "  int op, im;\n"
      "  initial begin\n"
      "    s.opcode = 8'hA5;\n"
      "    s.imm = 24'h123456;\n"
      "    op = s.opcode;\n"
      "    im = s.imm;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "  int whole;\n"
      "  initial #1 whole = m.s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* whole = f.ctx.FindVariable("whole");
  auto* op = f.ctx.FindVariable("m.op");
  auto* im = f.ctx.FindVariable("m.im");
  ASSERT_NE(whole, nullptr);
  ASSERT_NE(op, nullptr);
  ASSERT_NE(im, nullptr);
  EXPECT_EQ(whole->value.ToUint64(), 0xA5123456u);
  EXPECT_EQ(op->value.ToUint64(), 0xA5u);
  EXPECT_EQ(im->value.ToUint64(), 0x123456u);
}

TEST(PackedStructSimulation, ChildInstanceKeyedPatternPlacesEachMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  typedef struct packed { logic [7:0] opcode; logic [23:0] imm; } "
      "instruction_t;\n"
      "  instruction_t s;\n"
      "  int op;\n"
      "  initial begin\n"
      "    s = '{imm: 24'h0F1E2D, opcode: 8'h5A};\n"
      "    op = s.opcode;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "  int whole;\n"
      "  initial #1 whole = m.s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* whole = f.ctx.FindVariable("whole");
  auto* op = f.ctx.FindVariable("m.op");
  ASSERT_NE(whole, nullptr);
  ASSERT_NE(op, nullptr);
  EXPECT_EQ(whole->value.ToUint64(), 0x5A0F1E2Du);
  EXPECT_EQ(op->value.ToUint64(), 0x5Au);
}

TEST(PackedStructSimulation, WideMemberWriteLandsEveryWordOfItsValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  struct packed { logic [95:0] big; logic [7:0] low8; } s;\n"
      "  logic [95:0] w;\n"
      "  initial begin\n"
      "    s.big = 96'h0123_4567_89AB_CDEF_0F1E_2D3C;\n"
      "    s.low8 = 8'hA5;\n"
      "    w = s.big;\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.words[0].aval, 0xABCDEF0F1E2D3CA5u);
  EXPECT_EQ(var->value.words[1].aval, 0x0123456789u);
  auto* w = f.ctx.FindVariable("w");
  ASSERT_NE(w, nullptr);
  ASSERT_EQ(w->value.nwords, 2u);
  EXPECT_EQ(w->value.words[0].aval, 0x89ABCDEF0F1E2D3Cu);
  EXPECT_EQ(w->value.words[1].aval, 0x01234567u);
}

TEST(PackedStructSimulation, WideUnionMemberWriteReadsBackThroughTheOther) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  union packed { logic [95:0] w; logic [95:0] v; } u;\n"
      "  logic [95:0] rv;\n"
      "  initial begin\n"
      "    u.w = 96'hFEDC_BA98_7654_3210_0F0F_A5A5;\n"
      "    rv = u.v;\n"
      "  end\n"
      "endmodule\n",
      f, "rv");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.words[0].aval, 0x765432100F0FA5A5u);
  EXPECT_EQ(var->value.words[1].aval, 0xFEDCBA98u);
}

TEST(PackedStructSimulation, WideMemberWriteKeepsXAboveTheFirstWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  struct packed { logic [95:0] big; logic [7:0] low8; } s;\n"
      "  initial begin\n"
      "    s.big = 96'hxxxx_xxxx_89AB_CDEF_0F1E_2D3C;\n"
      "    s.low8 = 8'hA5;\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[0].aval, 0xABCDEF0F1E2D3CA5u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
  EXPECT_EQ(var->value.words[1].aval, 0xFFFFFFFF89u);
  EXPECT_EQ(var->value.words[1].bval, 0xFFFFFFFF00u);
}

TEST(PackedStructSimulation, WideMemberNonblockingWriteLandsEveryWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  struct packed { logic [95:0] big; logic [7:0] low8; } s;\n"
      "  logic [95:0] w;\n"
      "  initial begin\n"
      "    s.big <= 96'hFEDC_BA98_7654_3210_0F0F_A5A5;\n"
      "    s.low8 <= 8'h3C;\n"
      "    #1 w = s.big;\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[0].aval, 0x5432100F0FA5A53Cu);
  EXPECT_EQ(var->value.words[1].aval, 0xFEDCBA9876u);
  auto* w = f.ctx.FindVariable("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->value.words[1].aval, 0xFEDCBA98u);
}

TEST(PackedStructSimulation,
     QualifiedMemberLaidOutByItsPackageOverAnImportedSameNamedTypedef) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "package q;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "endpackage\n"
      "package r;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } pair_t;\n"
      "endpackage\n"
      "module t;\n"
      "  import r::*;\n"
      "  struct packed { q::pair_t p; logic [7:0] tail; } v;\n"
      "  logic [7:0] y;\n"
      "  initial begin\n"
      "    v.p.a = 8'd200;\n"
      "    v.p.b = 8'd7;\n"
      "    v.tail = 8'd9;\n"
      "    y = v.p.a;\n"
      "  end\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 24u);
  EXPECT_EQ(var->value.words[0].aval, 0xC80709u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.words[0].aval, 200u);
}

TEST(PackedStructSimulation, NamedAndEnumMembersKeepTheStructFourState) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef logic [3:0] nib_t;\n"
                       "  typedef enum logic [1:0] { A, B } e_t;\n"
                       "  struct packed { nib_t a; bit b; } s;\n"
                       "  struct packed { e_t e; bit b; } u;\n"
                       "  initial begin\n"
                       "    s.a = 'x;\n"
                       "    u.e = e_t'('x);\n"
                       "    $display(\"%b %b\", s.a, u.e);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "xxxx xx\n");
}

TEST(PackedStructSimulation, AMemberSizedByAParameterTakesEachInstancesValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m #(parameter int W = 2);\n"
                       "  typedef struct packed {\n"
                       "    logic [W-1:0] hi;\n"
                       "    logic [W-1:0] lo;\n"
                       "  } p_t;\n"
                       "  p_t p;\n"
                       "  initial begin\n"
                       "    #W;\n"
                       "    p = '1;\n"
                       "    p.lo = 0;\n"
                       "    $display(\"%0d %0d %0d\", W, $bits(p), p);\n"
                       "  end\n"
                       "endmodule\n"
                       "module t;\n"
                       "  m #(4) a();\n"
                       "  m #(8) b();\n"
                       "endmodule\n",
                       f),
            "4 8 240\n8 16 65280\n");
}

TEST(PackedStructSimulation, ANestedMembersParameterDimensionsAreFolded) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  localparam int W = 3;\n"
                 "  typedef struct packed {\n"
                 "    struct packed { logic [W-1:0] v; } [1:0][W-1:0] g;\n"
                 "  } g_t;\n"
                 "  g_t s;\n"
                 "  initial $display(\"%0d\", $bits(s));\n"
                 "endmodule\n",
                 f),
      "18\n");
}

TEST(PackedStructSimulation, ATypedefMembersOwnPackedDimensionsStackOnIt) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef logic [3:0] nib_t;\n"
                 "  typedef struct packed { nib_t [1:0] x; logic y; } s_t;\n"
                 "  s_t s;\n"
                 "  initial begin\n"
                 "    s = 9'h1A5;\n"
                 "    $display(\"%0d %0d %0d %0d\", $bits(s), $bits(s.x), "
                 "s.x, s.y);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "9 8 210 1\n");
}

TEST(PackedStructSimulation, AnInPlaceStructsStateIsItsMembers) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  function automatic struct packed {logic [3:0] a;} "
                       "fl(input struct packed {logic [3:0] a;} x);\n"
                       "    return x;\n"
                       "  endfunction\n"
                       "  function automatic struct packed {bit [3:0] a;} "
                       "fb(input struct packed {bit [3:0] a;} x);\n"
                       "    return x;\n"
                       "  endfunction\n"
                       "  initial $display(\"%b %b\", fl(4'b1x0z), "
                       "fb(4'b1x0z));\n"
                       "endmodule\n",
                       f),
            "1x0z 1000\n");
}

TEST(PackedStructSimulation, AnInPlaceStructOfATypedefMemberTakesItsState) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef logic [3:0] n4_t;\n"
                       "module t;\n"
                       "  typedef bit [3:0] b4_t;\n"
                       "  typedef logic [3:0] l4_t;\n"
                       "  function automatic void fl(struct packed {n4_t a;} "
                       "s);\n"
                       "    $display(\"%b\", s);\n"
                       "  endfunction\n"
                       "  function automatic void fm(struct packed {l4_t a;} "
                       "s);\n"
                       "    $display(\"%b\", s);\n"
                       "  endfunction\n"
                       "  function automatic void fb(struct packed {b4_t a;} "
                       "s);\n"
                       "    $display(\"%b\", s);\n"
                       "  endfunction\n"
                       "  function automatic void fn(struct packed {struct "
                       "packed {n4_t a;} s;} s);\n"
                       "    $display(\"%b\", s);\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    fl(4'b1x0z);\n"
                       "    fm(4'bz1x0);\n"
                       "    fb(4'b1x0z);\n"
                       "    fn(4'b1x0z);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1x0z\nz1x0\n1000\n1x0z\n");
}

TEST(PackedStructSimulation, AMemberWrittenWithATypeNameTakesItsWidth) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef logic [5:0] w_t;\n"
                       "typedef struct packed { w_t a; bit c; } us_t;\n"
                       "package p;\n"
                       "  typedef shortint h_t;\n"
                       "  typedef struct packed { h_t a; bit c; } ps_t;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  typedef logic [7:0] b_t;\n"
                       "  typedef enum byte { A, B } e_t;\n"
                       "  typedef struct packed { b_t a; e_t e; bit c; } s_t;\n"
                       "  typedef struct packed { b_t [2:0] a; } d_t;\n"
                       "  typedef union packed { b_t a; e_t e; } u_t;\n"
                       "  typedef union tagged packed { b_t a; e_t e; } tu_t;\n"
                       "  typedef struct packed { s_t inner; bit d; } n_t;\n"
                       "  typedef s_t [1:0] sa_t;\n"
                       "  initial begin\n"
                       "    $display(\"%0d %0d %0d %0d %0d\", $bits(us_t), "
                       "$bits(p::ps_t), $bits(s_t), $bits(d_t), $bits(u_t));\n"
                       "    $display(\"%0d %0d %0d\", $bits(tu_t), $bits(n_t), "
                       "$bits(sa_t));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "7 17 17 24 8\n9 18 34\n");
}

}  // namespace
