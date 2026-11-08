#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PassByValueSim, DefaultMechanismWithoutDirectionQualifier) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  function int add_ten(int v);\n"
      "    v = v + 10;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 5;\n"
      "    y = add_ten(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 5u}, {"y", 15u}});
}

TEST(PassByValueSim, AutomaticFunctionRetainsLocalCopy) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  function automatic int modify_arg(input int v);\n"
      "    v = v + 100;\n"
      "    return v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 7;\n"
      "    y = modify_arg(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}, {"y", 107u}});
}

TEST(PassByValueSim, TaskInputArgNotVisibleOutside) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  task modify(input int v);\n"
      "    v = v + 100;\n"
      "    y = v;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 7;\n"
      "    modify(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}, {"y", 107u}});
}

TEST(PassByValueSim, TaskDefaultDirectionArgPassedByValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  task apply(int v);\n"
      "    v = v + 50;\n"
      "    y = v;\n"
      "  endtask\n"
      "  initial begin\n"
      "    x = 4;\n"
      "    apply(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 4u}, {"y", 54u}});
}

TEST(PassByValueSim, MultipleArgsCopiedIndependently) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, result;\n"
      "  function int swap_and_add(int x, int y);\n"
      "    int tmp;\n"
      "    tmp = x;\n"
      "    x = y;\n"
      "    y = tmp;\n"
      "    return x + y;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a = 3;\n"
      "    b = 7;\n"
      "    result = swap_and_add(a, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 3u}, {"b", 7u}, {"result", 10u}});
}

TEST(PassByValueSim, RecursiveAutomaticUsesPerActivationStackCopy) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  function automatic int sum_down(int n);\n"
      "    if (n == 0) return 0;\n"
      "    return n + sum_down(n - 1);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result = sum_down(4);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 10u}});
}

TEST(PassByValueSim, SameSourceBoundToTwoFormalsCopiesIndependently) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, result;\n"
      "  function int scale_first_minus_second(int a, int b);\n"
      "    a = a * 10;\n"
      "    return a - b;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 7;\n"
      "    result = scale_first_minus_second(x, x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}, {"result", 63u}});
}

TEST(PassByValueSim, UnpackedArrayArgumentCopiedElementwise) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte packet [0:1];\n"
      "  int total;\n"
      "  function int sum_then_clobber(byte p [0:1]);\n"
      "    int s;\n"
      "    s = p[0] + p[1];\n"
      "    p[0] = 99;\n"
      "    p[1] = 99;\n"
      "    return s;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    packet[0] = 3;\n"
      "    packet[1] = 4;\n"
      "    total = sum_then_clobber(packet);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"packet[0]", 3u}, {"packet[1]", 4u}, {"total", 7u}});
}

TEST(PassByValueSim, TypedefNameInputFormalIsSizedByTheTypeItNames) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [3:0] nib;\n"
      "  int y;\n"
      "  function int take(input nib p);\n"
      "    return p;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    y = take(8'hFF);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 15u}});
}

TEST(PassByValueSim, TypedefNameTaskInputFormalIsSizedByTheTypeItNames) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [3:0] nib;\n"
      "  int y;\n"
      "  task take(input nib p, output int o);\n"
      "    o = p;\n"
      "  endtask\n"
      "  initial begin\n"
      "    y = 0;\n"
      "    take(8'hFF, y);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 15u}});
}

TEST(PassByValueSim, TypedefNameFormalWiderThanOneWordKeepsItsHighBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [39:0] wide;\n"
      "  logic [63:0] y;\n"
      "  function logic [63:0] take(input wide p);\n"
      "    return p;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    y = take(48'hFFFF00000001);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 1095216660481ull}});
}

TEST(PassByValueSim, ForwardDeclaredClassFormalKeepsTheWholeHandle) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "typedef class Packet;\n"
      "class Packet;\n"
      "  integer i = 42;\n"
      "endclass\n"
      "module t;\n"
      "  int y;\n"
      "  function integer read_i(Packet p);\n"
      "    read_i = p.i;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    Packet q;\n"
      "    q = new;\n"
      "    y = read_i(q);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 42u}});
}

TEST(PassByValueSim, ActualBoundToASameWidthTwoStateFormalKeepsItsUnknowns) {
  SimFixture f;
  auto* carried = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] carried;\n"
      "  bit [7:0] observed;\n"
      "  function bit [7:0] keep(bit [7:0] copy_in);\n"
      "    return copy_in;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    carried = 8'b0z1x0110;\n"
      "    observed = keep(carried);\n"
      "  end\n"
      "endmodule\n",
      f, "carried");
  ASSERT_NE(carried, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* observed = f.ctx.FindVariable("observed");
  ASSERT_NE(observed, nullptr);
  EXPECT_EQ(carried->value.words[0].aval & 0xFFu, 0x36u);
  EXPECT_EQ(carried->value.words[0].bval & 0xFFu, 0x50u);
  EXPECT_EQ(observed->value.words[0].aval & 0xFFu, 0x26u);
  EXPECT_EQ(observed->value.words[0].bval & 0xFFu, 0x00u);
}

TEST(PassByValueSim, ArrayElementActualKeepsItsUnknownsAcrossTheBinding) {
  SimFixture f;
  auto* lane = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] lanes [0:1];\n"
      "  bit [7:0] copied;\n"
      "  function bit [7:0] relay(bit [7:0] one_lane);\n"
      "    return one_lane;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    lanes[1] = 8'b11x0z101;\n"
      "    copied = relay(lanes[1]);\n"
      "  end\n"
      "endmodule\n",
      f, "lanes[1]");
  ASSERT_NE(lane, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* copied = f.ctx.FindVariable("copied");
  ASSERT_NE(copied, nullptr);
  EXPECT_EQ(lane->value.words[0].aval & 0xFFu, 0xE5u);
  EXPECT_EQ(lane->value.words[0].bval & 0xFFu, 0x28u);
  EXPECT_EQ(copied->value.words[0].aval & 0xFFu, 0xC5u);
  EXPECT_EQ(copied->value.words[0].bval & 0xFFu, 0x00u);
}

TEST(PassByValueSim, NarrowerFormalTruncatesWithoutTouchingTheActual) {
  SimFixture f;
  auto* source_bits = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] source_bits;\n"
      "  int read_back;\n"
      "  function int shrink(bit [3:0] narrow_in);\n"
      "    return narrow_in;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    source_bits = 8'b1x01z100;\n"
      "    read_back = shrink(source_bits);\n"
      "  end\n"
      "endmodule\n",
      f, "source_bits");
  ASSERT_NE(source_bits, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* read_back = f.ctx.FindVariable("read_back");
  ASSERT_NE(read_back, nullptr);
  EXPECT_EQ(source_bits->value.words[0].aval & 0xFFu, 0xD4u);
  EXPECT_EQ(source_bits->value.words[0].bval & 0xFFu, 0x48u);
  EXPECT_EQ(read_back->value.words[0].aval & 0xFFu, 0x4u);
  EXPECT_EQ(read_back->value.words[0].bval & 0xFFu, 0x0u);
}

TEST(PassByValueSim, AssocFormalElementBitsAreNotTheActualsWords) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] aa[int];\n"
      "  logic [7:0] r;\n"
      "  task automatic poke(logic [7:0] a[int]);\n"
      "    a[5][3:0] = 4'hF;\n"
      "  endtask\n"
      "  initial begin\n"
      "    aa[5] = 8'h00;\n"
      "    poke(aa);\n"
      "    r = aa[5];\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0x00u);
}

TEST(PassByValueSim, QueueFormalElementWriteIsNotVisibleOutside) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] qu[$];\n"
      "  logic [7:0] r;\n"
      "  task automatic poke(logic [7:0] a[$]);\n"
      "    a[0] = 8'hFF;\n"
      "  endtask\n"
      "  initial begin\n"
      "    qu.push_back(8'h11);\n"
      "    poke(qu);\n"
      "    r = qu[0];\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0x11u);
}

TEST(PassByValueSim, FixedArrayFormalElementWriteIsNotVisibleOutside) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] arr[0:1];\n"
      "  logic [7:0] r;\n"
      "  task automatic poke(logic [7:0] a[0:1]);\n"
      "    a[1] = 8'hFF;\n"
      "  endtask\n"
      "  initial begin\n"
      "    arr[1] = 8'h11;\n"
      "    poke(arr);\n"
      "    r = arr[1];\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0x11u);
}

TEST(PassByValueSim, QueueFormalNamedLikeTheModulesIsItsOwnCopy) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int r;\n"
      "  task automatic fill(input int q[$]);\n"
      "    q[0] = 99;\n"
      "  endtask\n"
      "  initial begin\n"
      "    q.push_back(7);\n"
      "    fill(q);\n"
      "    r = q[0];\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 7u);
}

TEST(PassByValueSim, AssocFormalNamedLikeTheModulesIsItsOwnCopy) {
  auto v = RunAndGet(
      "module t;\n"
      "  int aa[int];\n"
      "  int r;\n"
      "  task automatic fill(input int aa[int]);\n"
      "    aa[5] = 99;\n"
      "  endtask\n"
      "  initial begin\n"
      "    aa[5] = 7;\n"
      "    fill(aa);\n"
      "    r = aa[5];\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 7u);
}

TEST(PassByValueSim, QueueFormalCopyDoesNotOutliveTheCall) {
  auto v = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int r;\n"
      "  task automatic fill(input int q[$]);\n"
      "    q.push_back(99);\n"
      "  endtask\n"
      "  initial begin\n"
      "    q.push_back(7);\n"
      "    fill(q);\n"
      "    r = q.size();\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 1u);
}

TEST(PassByValueSim, TypedefSignedFormalSignExtendsIntoAWiderTarget) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef byte b_t;\n"
      "  int r;\n"
      "  function int widen(input b_t p);\n"
      "    return p;\n"
      "  endfunction\n"
      "  initial r = widen(-1);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0xFFFFFFFFu);
}

TEST(PassByValueSim, TypedefExplicitlySignedFormalSignExtends) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef logic signed [7:0] s8_t;\n"
      "  int r;\n"
      "  function int widen(input s8_t p);\n"
      "    return p;\n"
      "  endfunction\n"
      "  initial r = widen(-1);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0xFFFFFFFFu);
}

TEST(PassByValueSim, TypedefSignedFormalComparesAsSigned) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef byte b_t;\n"
      "  int r;\n"
      "  function int is_negative(input b_t p);\n"
      "    return (p < 0) ? 1 : 0;\n"
      "  endfunction\n"
      "  initial r = is_negative(-1);\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 1u);
}

TEST(PassByValueSim, TypedefSignedBodyLocalSignExtends) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef byte b_t;\n"
      "  int r;\n"
      "  function int widen();\n"
      "    static b_t p = -1;\n"
      "    return p;\n"
      "  endfunction\n"
      "  initial r = widen();\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0xFFFFFFFFu);
}

TEST(PassByValueSim, FixedUnpackedArrayTypedefFormalIsNotSizedToOneElement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef byte b4_t[4];\n"
      "  int y;\n"
      "  function automatic int arrival_bits(input b4_t v);\n"
      "    return $bits(v);\n"
      "  endfunction\n"
      "  initial y = arrival_bits('{8'h11, 8'h22, 8'h33, 8'h44});\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 32u}});
}

TEST(PassByValueSim, ChildInstanceStructActualBindsTheFormalsLayout) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  typedef struct packed { logic [7:0] opcode; logic [23:0] imm; } "
      "instruction_t;\n"
      "  instruction_t s;\n"
      "  int r;\n"
      "  function automatic int get_op(input instruction_t a);\n"
      "    return a.opcode;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    s.opcode = 8'hA5;\n"
      "    s.imm = 24'h123456;\n"
      "    r = get_op(s);\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"m.r", 0xA5u}});
}

TEST(PassByValueSim, InlineStructFormalBoundFromAStructVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { int a, b; } pair_t;\n"
      "  pair_t x;\n"
      "  int y;\n"
      "  function int f(struct packed { int a, b; } s);\n"
      "    return s.a * 10 + s.b;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = '{1, 2};\n"
      "    y = f(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 12u}});
}

TEST(PassByValueSim, InlineStructFormalBoundFromACallResult) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { int a, b; } pair_t;\n"
      "  int y;\n"
      "  function pair_t g();\n"
      "    return '{3, 4};\n"
      "  endfunction\n"
      "  function int f(struct packed { int a, b; } s);\n"
      "    return s.a * 10 + s.b;\n"
      "  endfunction\n"
      "  initial y = f(g());\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 34u}});
}

TEST(PassByValueSim, InlinePackedUnionFormalReadsItsSecondMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] w = 16'hABCD;\n"
      "  int y;\n"
      "  function int f(union packed { logic [15:0] whole;"
      " struct packed { logic [7:0] hi, lo; } h; } u);\n"
      "    return u.h.lo;\n"
      "  endfunction\n"
      "  initial y = f(w);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 0xCDu}});
}

TEST(PassByValueSim, TypedefStructFormalPlacesAKeyedPatternByMemberName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a, b; } pair_t;\n"
      "  int y;\n"
      "  function int f(pair_t s);\n"
      "    return s.a * 10 + s.b;\n"
      "  endfunction\n"
      "  initial y = f('{b: 2, a: 1});\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 12u}});
}

TEST(PassByValueSim, TypedefStructFormalPlacesANarrowPositionalPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { int a, b; } pair_t;\n"
      "  int y;\n"
      "  function int f(pair_t s);\n"
      "    return s.a * 10 + s.b;\n"
      "  endfunction\n"
      "  initial y = f('{8'd1, 8'd2});\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 12u}});
}

TEST(PassByValueSim, InlineStructFormalPlacesAKeyedPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int y;\n"
      "  function int f(struct packed { int a, b; } s);\n"
      "    return s.a * 10 + s.b;\n"
      "  endfunction\n"
      "  initial y = f('{b: 2, a: 1});\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 12u}});
}

TEST(PassByValueSim, TypedefStructFormalPlacesANestedMemberByName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { int a, b; } pair_t;\n"
      "  typedef struct packed { pair_t p; int c; } trip_t;\n"
      "  pair_t x;\n"
      "  int y;\n"
      "  function int f(trip_t s);\n"
      "    return s.p.a * 100 + s.p.b * 10 + s.c;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = '{1, 2};\n"
      "    y = f('{c: 3, p: x});\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"y", 123u}});
}

}  // namespace
