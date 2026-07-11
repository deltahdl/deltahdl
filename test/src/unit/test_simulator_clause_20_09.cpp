#include <iostream>
#include <sstream>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// Runs a single-module source through elaboration and simulation while
// capturing everything the run writes to stdout.
inline std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) {
    LowerAndRun(design, f);
  }
  std::cout.rdbuf(old_buf);
  return captured.str();
}

TEST(UtilitySystemTaskTest, CountonesZero) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$countones", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(UtilitySystemTaskTest, CountonesAllBits) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$countones", {MakeInt(f.arena, 0xFF)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 8u);
}

TEST(UtilitySystemTaskTest, CountonesSparse) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$countones", {MakeInt(f.arena, 0b10101)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(UtilitySystemTaskTest, OnehotTrue) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot", {MakeInt(f.arena, 4)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(UtilitySystemTaskTest, OnehotFalseZero) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(UtilitySystemTaskTest, OnehotFalseMultiple) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot", {MakeInt(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(UtilitySystemTaskTest, Onehot0True) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot0", {MakeInt(f.arena, 0)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(UtilitySystemTaskTest, Onehot0TrueOneBit) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot0", {MakeInt(f.arena, 8)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(UtilitySystemTaskTest, Onehot0FalseMultiple) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$onehot0", {MakeInt(f.arena, 3)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(UtilitySystemTaskTest, IsunknownFalse) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$isunknown", {MakeInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(UtilitySystemTaskTest, IsunknownTrueXVar) {
  SimFixture f;

  f.ctx.CreateVariable("xvar", 8);
  auto* expr = MakeSysCall(f.arena, "$isunknown", {MakeId(f.arena, "xvar")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §20.9: a wider control_bit is reduced to its low bit before matching. Here
// 0xE has LSB 0, so the call counts the zero bits of the 32-bit operand
// 0x000000A5 -> 32 - popcount(0xA5) = 28.
TEST(UtilitySystemTaskTest, CountbitsControlBitOnlyLsbUsed) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$countbits",
                         {MkInt(f.arena, 0xA5), MkInt(f.arena, 0xE)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 28u);
}

// §20.9: a control_bit value repeated in the argument list contributes the
// same as a single occurrence, so calling with '1 twice yields the same
// result as calling with '1 once.
TEST(UtilitySystemTaskTest, CountbitsControlBitDeduplicated) {
  SysTaskFixture f;
  auto* once = MkSysCall(f.arena, "$countbits",
                         {MkInt(f.arena, 0xA5), MkInt(f.arena, 1)});
  auto* twice =
      MkSysCall(f.arena, "$countbits",
                {MkInt(f.arena, 0xA5), MkInt(f.arena, 1), MkInt(f.arena, 1)});
  auto r_once = EvalExpr(once, f.ctx, f.arena);
  auto r_twice = EvalExpr(twice, f.ctx, f.arena);
  EXPECT_EQ(r_once.ToUint64(), r_twice.ToUint64());
  EXPECT_EQ(r_twice.ToUint64(), 4u);
}

// §20.9: the control_bit may be a variable, not a constant. The simulator
// must evaluate the control_bit expression at call time and use its LSB.
// Here ctrl is a 1-bit variable holding 1, so the call counts the four 1-bits
// of 0xA5.
TEST(UtilitySystemTaskTest, CountbitsVariableControlBitAtRuntime) {
  SysTaskFixture f;
  MakeVar(f, "ctrl", 1, 1);
  auto* expr = MakeSysCall(f.arena, "$countbits",
                           {MakeInt(f.arena, 0xA5), MakeId(f.arena, "ctrl")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 4u);
}

// §20.9: $countones is equivalent to $countbits(expression, '1), so x/z bits
// in the expression must not be counted. Build an 8-bit value whose bit 0 is
// 1 and whose upper nibble is x; only the single known 1-bit must register.
TEST(UtilitySystemTaskTest, CountonesIgnoresUnknownBits) {
  SysTaskFixture f;
  auto* var = f.ctx.CreateVariable("mix", 8);
  var->value.words[0].aval = 0x01;
  var->value.words[0].bval = 0xF0;
  auto* expr = MakeSysCall(f.arena, "$countones", {MakeId(f.arena, "mix")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §20.9: $isunknown is true when $countbits(expression, 'x, 'z) is non-zero,
// so z-only operands must register as unknown just like x-only operands do.
// Convert the default-x variable bits into z by also setting aval, leaving
// bval set.
TEST(UtilitySystemTaskTest, IsunknownTrueZVar) {
  SysTaskFixture f;
  auto* var = f.ctx.CreateVariable("zvar", 8);
  for (uint32_t i = 0; i < var->value.nwords; ++i) {
    var->value.words[i].aval = ~uint64_t{0};
  }
  auto* expr = MakeSysCall(f.arena, "$isunknown", {MakeId(f.arena, "zvar")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §20.9: the expression argument shall be of a bit-stream type and is treated
// as the vector {>>{expression}} produces (§11.4.14). A fixed unpacked array is
// such a type, so $countones must count the one-bits across every element, not
// treat the bare array name as an empty operand. arr[0]=4'b1011 (3 ones) and
// arr[1]=4'b0100 (1 one) pack to eight bits with four ones total.
TEST(UtilitySystemTaskTest, CountonesPacksUnpackedArrayOperand) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  logic [3:0] arr [0:1];\n"
      "  int c;\n"
      "  initial begin\n"
      "    arr[0] = 4'b1011;\n"
      "    arr[1] = 4'b0100;\n"
      "    c = $countones(arr);\n"
      "    $display(\"%0d\", c);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

// §20.9: a queue is a (dynamically sized) bit-stream type, so $countbits with a
// queue operand counts matching bits across all live elements. Two 4-bit
// elements 4'b1011 (3 ones) and 4'b0001 (1 one) give four one-bits.
TEST(UtilitySystemTaskTest, CountbitsPacksQueueOperand) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  logic [3:0] q[$];\n"
      "  int c;\n"
      "  initial begin\n"
      "    q.push_back(4'b1011);\n"
      "    q.push_back(4'b0001);\n"
      "    c = $countbits(q, 1'b1);\n"
      "    $display(\"%0d\", c);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

// §20.9: $isunknown is true when the packed bit-stream operand holds any x or
// z. The unknown bits live in the second queue element, which only registers
// once the queue is packed as {>>{q}} rather than read as a bare (empty)
// operand.
TEST(UtilitySystemTaskTest, IsunknownDetectsUnknownInQueueOperand) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  logic [3:0] q[$];\n"
      "  initial begin\n"
      "    q.push_back(4'b1010);\n"
      "    q.push_back(4'b00x1);\n"
      "    $display(\"%0d\", $isunknown(q));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

// §20.9: a fully known bit-stream operand has no x or z, so $isunknown is 0
// even across a multi-element unpacked array.
TEST(UtilitySystemTaskTest, IsunknownFalseForKnownArrayOperand) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  logic [3:0] arr [0:1];\n"
      "  initial begin\n"
      "    arr[0] = 4'b1010;\n"
      "    arr[1] = 4'b0101;\n"
      "    $display(\"%0d\", $isunknown(arr));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

// §20.9: $onehot over a bit-stream operand is true only when exactly one bit is
// set across the whole packed vector. A single set bit in one array element
// must register as one-hot; a second set bit anywhere in the operand must not.
TEST(UtilitySystemTaskTest, OnehotAcrossUnpackedArrayOperand) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  logic [3:0] arr [0:1];\n"
      "  initial begin\n"
      "    arr[0] = 4'b0000;\n"
      "    arr[1] = 4'b0100;\n"
      "    $display(\"%0d\", $onehot(arr));\n"
      "    arr[0] = 4'b0001;\n"
      "    $display(\"%0d\", $onehot(arr));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n0\n");
}

// §20.9: $countbits(expr, 'x, 'z) counts the x/z bits, and 'x and 'z select
// distinct bit values -- an x-only control bit must not count z bits and vice
// versa. Drive an 8-bit variable whose low nibble is x x z z from real source:
// $countbits(v,'x)=2 (x only), $countbits(v,'x,'z)=4 (x and z), and
// $countbits(v,'1,'0)=4 (only the four known bits, x/z excluded).
TEST(UtilitySystemTaskTest, CountbitsCountsUnknownBitsByValue) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  logic [7:0] v;\n"
      "  int cx, cxz, ckn;\n"
      "  initial begin\n"
      "    v = 8'b1010xxzz;\n"
      "    cx  = $countbits(v, 1'bx);\n"
      "    cxz = $countbits(v, 1'bx, 1'bz);\n"
      "    ckn = $countbits(v, 1'b1, 1'b0);\n"
      "    $display(\"%0d %0d %0d\", cx, cxz, ckn);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 4 4\n");
}

// §20.9 (dep §11.4.14 / §7.5): a dynamic array is a bit-stream type, so
// $countones counts one-bits across all of its live elements. The array is
// built from real source with a '{...} initializer and packed as {>>{d}}. Its
// three elements contribute 3 + 1 + 4 = 8 one-bits. (This form also covers
// dynamic arrays, whose elements live in a queue backing store rather than in
// named element variables.)
TEST(UtilitySystemTaskTest, CountonesPacksDynamicArrayOperand) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  logic [3:0] d[] = '{4'b1011, 4'b0100, 4'b1111};\n"
      "  int c;\n"
      "  initial begin\n"
      "    c = $countones(d);\n"
      "    $display(\"%0d\", c);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "8\n");
}

// §20.9 (dep §11.4.14): a packed struct is a bit-stream type, so $countones
// counts one-bits across all of its fields. Built from a real struct
// declaration and member assignments: hi=4'b1011 (3) and lo=4'b0001 (1) give
// four one-bits.
TEST(UtilitySystemTaskTest, CountonesPacksPackedStructOperand) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  int c;\n"
      "  initial begin\n"
      "    p.hi = 4'b1011;\n"
      "    p.lo = 4'b0001;\n"
      "    c = $countones(p);\n"
      "    $display(\"%0d\", c);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

// §20.9: return types -- $countbits and $countones return int (32 bits), while
// $onehot, $onehot0, and $isunknown return bit (a single bit). This is a
// property of the function alone and does not depend on how the operand is
// produced, so it is observed directly on the evaluated result.
TEST(UtilitySystemTaskTest, BitVectorFunctionReturnWidths) {
  SysTaskFixture f;
  auto* countbits = MakeSysCall(f.arena, "$countbits",
                                {MakeInt(f.arena, 0xA5), MakeInt(f.arena, 1)});
  auto* countones =
      MakeSysCall(f.arena, "$countones", {MakeInt(f.arena, 0xA5)});
  auto* onehot = MakeSysCall(f.arena, "$onehot", {MakeInt(f.arena, 4)});
  auto* onehot0 = MakeSysCall(f.arena, "$onehot0", {MakeInt(f.arena, 4)});
  auto* isunknown = MakeSysCall(f.arena, "$isunknown", {MakeInt(f.arena, 4)});
  EXPECT_EQ(EvalExpr(countbits, f.ctx, f.arena).width, 32u);
  EXPECT_EQ(EvalExpr(countones, f.ctx, f.arena).width, 32u);
  EXPECT_EQ(EvalExpr(onehot, f.ctx, f.arena).width, 1u);
  EXPECT_EQ(EvalExpr(onehot0, f.ctx, f.arena).width, 1u);
  EXPECT_EQ(EvalExpr(isunknown, f.ctx, f.arena).width, 1u);
}

}  // namespace
