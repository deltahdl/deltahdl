#include <gtest/gtest.h>

#include <cstdint>
#include <string>

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

std::string RunBitVector(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

TEST(BitVectorFunctionSim,
     DISABLED_ASignedIntResultKeepsTheEnclosingExpressionSigned) {
  EXPECT_EQ(RunBitVector("module t;\n"
                         "  logic [7:0] v = 8'b0000_0111;\n"
                         "  initial $display(\"%0d %0d %0d %0d %s %s %s %s\", "
                         "($countones(v) - 5) < 0,\n"
                         "    $countones(v) > -1, ($countbits(v, 1) - 5) < 0, "
                         "$countbits(v, 1) > -1,\n"
                         "    $typename($countbits(v, 1)), "
                         "$typename($countones(v)), $typename($onehot(v)),\n"
                         "    $typename($onehot0(v)));\n"
                         "endmodule\n"),
            "1 1 1 1 int int bit bit\n");
}

TEST(BitVectorFunctionSim, AContinuousAssignmentFollowsItsOperand) {
  EXPECT_EQ(RunBitVector("module t;\n"
                         "  logic [7:0] v = 8'b0000_0011;\n"
                         "  int c;\n"
                         "  assign c = $countones(v);\n"
                         "  initial begin\n"
                         "    #1 $display(\"%0d\", c);\n"
                         "    v = 8'b1111_0111;\n"
                         "    #1 $display(\"%0d\", c);\n"
                         "  end\n"
                         "endmodule\n"),
            "2\n7\n");
}

TEST(BitVectorFunctionSim, AClassMethodAPackageFunctionAndALetUseTheResult) {
  EXPECT_EQ(RunBitVector(
                "package pk;\n"
                "  function automatic int ones(logic [7:0] x);\n"
                "    return $countones(x);\n"
                "  endfunction\n"
                "endpackage\n"
                "class C;\n"
                "  function bit hot(logic [3:0] x);\n"
                "    return $onehot(x);\n"
                "  endfunction\n"
                "endclass\n"
                "module t;\n"
                "  let my_one_hot_known(myvec) = (($countones(myvec) == 1) &&\n"
                "                                 ($countbits(myvec, 'x, 'z) "
                "== 0));\n"
                "  C h = new;\n"
                "  initial $display(\"%0d %0d %0d %0d\", pk::ones(8'hF0), "
                "h.hot(4'b0100),\n"
                "    my_one_hot_known(4'b0100), my_one_hot_known(4'b01x0));\n"
                "endmodule\n"),
            "4 1 1 0\n");
}

TEST(BitVectorFunctionSim, ARandomizedValueSatisfiesABitVectorConstraint) {
  EXPECT_EQ(RunBitVector("class C;\n"
                         "  rand bit [7:0] b;\n"
                         "  constraint c { $countones(b) == 3; }\n"
                         "endclass\n"
                         "module t;\n"
                         "  C h = new;\n"
                         "  int ok = 1;\n"
                         "  initial begin\n"
                         "    repeat (8) begin\n"
                         "      void'(h.randomize());\n"
                         "      if ($countones(h.b) != 3) ok = 0;\n"
                         "    end\n"
                         "    $display(\"%0d\", ok);\n"
                         "  end\n"
                         "endmodule\n"),
            "1\n");
}

TEST(BitVectorFunctionSim, OnehotZeroIgnoresXAndZBits) {
  EXPECT_EQ(RunBitVector("module t;\n"
                         "  initial $display(\"%0d %0d %0d\", "
                         "$onehot0(8'bxx00_0000), $onehot0(8'bx000_0001),\n"
                         "    $onehot0(8'bz001_0001));\n"
                         "endmodule\n"),
            "1 1 0\n");
}

TEST(BitVectorFunctionSim, OnehotCountsOnlyItsOnesBesideXAndZBits) {
  EXPECT_EQ(RunBitVector("module t;\n"
                         "  initial $display(\"%0d %0d %0d %0d\", "
                         "$onehot(8'b0000_x100), $onehot(8'b0000_z100),\n"
                         "    $onehot(8'b0x00_z000), $onehot(8'b0x01_0100));\n"
                         "endmodule\n"),
            "1 1 0 0\n");
}

TEST(BitVectorFunctionSim, AStringAndAnUnpackedStructAreStreamed) {
  EXPECT_EQ(
      RunBitVector("module t;\n"
                   "  typedef struct {logic [3:0] a; logic [3:0] b;} s_t;\n"
                   "  string s = \"AC\";\n"
                   "  s_t st;\n"
                   "  initial begin\n"
                   "    st.a = 4'b0111;\n"
                   "    st.b = 4'b000x;\n"
                   "    $display(\"%0d %0d %0d\", $countones(s), "
                   "$countones(st), $isunknown(st));\n"
                   "  end\n"
                   "endmodule\n"),
      "5 3 1\n");
}

TEST(BitVectorFunctionSim, BitSelectsOfAVariableAreControlBitsInAnAssertion) {
  EXPECT_EQ(RunBitVector("module t;\n"
                         "  logic [1:0] bad_bits;\n"
                         "  logic [31:0] myvec;\n"
                         "  logic done;\n"
                         "  int fails = 0;\n"
                         "  initial begin\n"
                         "    myvec = 32'h0000_00zz;\n"
                         "    done = 0;\n"
                         "    bad_bits[0] = 'x;\n"
                         "    bad_bits[1] = 'x;\n"
                         "    a1: assert ($countbits(myvec, bad_bits[0], "
                         "bad_bits[1]) == 0) else fails++;\n"
                         "    done = 1;\n"
                         "    bad_bits[0] = 'x;\n"
                         "    bad_bits[1] = 'z;\n"
                         "    a2: assert ($countbits(myvec, bad_bits[0], "
                         "bad_bits[1]) == 0) else fails++;\n"
                         "    $display(\"%0d %0d\", fails, $countbits(myvec, "
                         "bad_bits[0], bad_bits[1]));\n"
                         "  end\n"
                         "endmodule\n"),
            "1 8\n");
}

TEST(BitVectorFunctionSim, AZControlBitCountsOnlyZBits) {
  EXPECT_EQ(RunBitVector("module t;\n"
                         "  logic [7:0] v = 8'bzzx1_x0zz;\n"
                         "  initial $display(\"%0d %0d\", $countbits(v, 1'bz), "
                         "$countbits(v, 1'bx));\n"
                         "endmodule\n"),
            "4 2\n");
}

TEST(BitVectorFunctionSim, UnbasedUnsizedLiteralsAreControlBits) {
  EXPECT_EQ(
      RunBitVector(
          "module t;\n"
          "  logic [7:0] v = 8'bz1x0_110x;\n"
          "  initial $display(\"%0d %0d %0d %0d %0d\", $countbits(v, '1), "
          "$countbits(v, '0),\n"
          "    $countbits(v, 'x), $countbits(v, 'z), $countbits(v, '1, '1));\n"
          "endmodule\n"),
      "3 2 2 1 3\n");
}

}  // namespace
