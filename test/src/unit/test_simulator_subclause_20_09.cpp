#include <gtest/gtest.h>

#include <cstdint>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

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

TEST(UtilitySystemTaskTest, CountbitsControlBitOnlyLsbUsed) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$countbits",
                         {MkInt(f.arena, 0xA5), MkInt(f.arena, 0xE)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 28u);
}

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

TEST(UtilitySystemTaskTest, CountbitsVariableControlBitAtRuntime) {
  SysTaskFixture f;
  MakeVar(f, "ctrl", 1, 1);
  auto* expr = MakeSysCall(f.arena, "$countbits",
                           {MakeInt(f.arena, 0xA5), MakeId(f.arena, "ctrl")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 4u);
}

TEST(UtilitySystemTaskTest, CountonesIgnoresUnknownBits) {
  SysTaskFixture f;
  auto* var = f.ctx.CreateVariable("mix", 8);
  var->value.words[0].aval = 0x01;
  var->value.words[0].bval = 0xF0;
  auto* expr = MakeSysCall(f.arena, "$countones", {MakeId(f.arena, "mix")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

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
