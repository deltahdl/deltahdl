#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

static Variable* RunAndFind(const std::string& src, SimFixture& f,
                            const char* var_name) {
  auto* design = ElaborateSrc(src, f);
  if (!design) return nullptr;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return f.ctx.FindVariable(var_name);
}

TEST(ParameterizedSubroutineSim, ParameterizedStaticFunctionReturnsValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class Doubler#(parameter W = 8);\n"
      "  static function logic [W-1:0] double_val(\n"
      "      input logic [W-1:0] x);\n"
      "    return x * 2;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = Doubler#(8)::double_val(8'd21);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"result", 42u}});
}

TEST(ParameterizedSubroutineSim, VirtualClassIsAbstract) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int get_w; get_w = W; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* info = f.ctx.FindClassType("C");
  ASSERT_NE(info, nullptr);
  EXPECT_TRUE(info->is_abstract);
}

TEST(ParameterizedSubroutineSim, StaticMethodRegistered) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int get_w; get_w = W; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* info = f.ctx.FindClassType("C");
  ASSERT_NE(info, nullptr);
  auto it = info->methods.find("get_w");
  ASSERT_NE(it, info->methods.end());
  EXPECT_TRUE(it->second->is_static_method);
}

TEST(ParameterizedSubroutineSim, NonVirtualParameterizedClass) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class C #(parameter W = 8);\n"
      "    static function int get_w; get_w = W; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* info = f.ctx.FindClassType("C");
  ASSERT_NE(info, nullptr);
  EXPECT_FALSE(info->is_abstract);
  EXPECT_NE(info->methods.find("get_w"), info->methods.end());
}

TEST(ParameterizedSubroutineSim, SimpleParameterReturn) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int get_w; get_w = W; endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(16)::get_w();\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(ParameterizedSubroutineSim, DefaultParameterValue) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter A = 10, parameter B = 5);\n"
      "    static function int get_b; get_b = B; endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(20)::get_b();\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(ParameterizedSubroutineSim, DefaultParamClog2) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter DECODE_W = 8,\n"
      "                     parameter ENCODE_W = $clog2(DECODE_W));\n"
      "    static function int get_enc_w;\n"
      "      get_enc_w = ENCODE_W;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(8)::get_enc_w();\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(ParameterizedSubroutineSim, MultipleSpecializations) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int get_w; get_w = W; endfunction\n"
      "  endclass\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = C#(8)::get_w();\n"
      "    r2 = C#(32)::get_w();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 8u}, {"r2", 32u}});
}

TEST(ParameterizedSubroutineSim, TwoParametersExplicit) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter A = 1, parameter B = 2);\n"
      "    static function int sum; sum = A + B; endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(10, 20)::sum();\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(ParameterizedSubroutineSim, ParameterArithmetic) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int doubled; doubled = W * 2; endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(7)::doubled();\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 14u);
}

TEST(ParameterizedSubroutineSim, ParameterIfElse) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int classify;\n"
      "      if (W > 16) classify = 2;\n"
      "      else if (W > 8) classify = 1;\n"
      "      else classify = 0;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(32)::classify();\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(ParameterizedSubroutineSim, MethodWithInputArg) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int add_w(input int x);\n"
      "      add_w = x + W;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(10)::add_w(5);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(ParameterizedSubroutineSim, MethodWithTwoArgs) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter W = 0);\n"
      "    static function int weighted_sum(input int a, input int b);\n"
      "      weighted_sum = a * W + b;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(3)::weighted_sum(4, 5);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 17u);
}

TEST(ParameterizedSubroutineSim, TwoMethodsSameClass) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int get_w; get_w = W; endfunction\n"
      "    static function int get_w_plus_one;\n"
      "      get_w_plus_one = W + 1;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = C#(10)::get_w();\n"
      "    r2 = C#(10)::get_w_plus_one();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 10u}, {"r2", 11u}});
}

TEST(ParameterizedSubroutineSim, ContinuousAssignCall) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int get_w; get_w = W; endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  assign result = C#(42)::get_w();\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(ParameterizedSubroutineSim, AlwaysCombCall) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int get_w; get_w = W; endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  always_comb result = C#(99)::get_w();\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(ParameterizedSubroutineSim, DifferentSpecsDifferentResults) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  virtual class C #(parameter W = 0);\n"
      "    static function int mask;\n"
      "      mask = (1 << W) - 1;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int r4, r8;\n"
      "  initial begin\n"
      "    r4 = C#(4)::mask();\n"
      "    r8 = C#(8)::mask();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r4", 15u}, {"r8", 255u}});
}

TEST(ParameterizedSubroutineSim, ParameterSubtract) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int max_idx;\n"
      "      max_idx = W - 1;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(16)::max_idx();\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(ParameterizedSubroutineSim, ChainedParamExpr) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter W = 0);\n"
      "    static function int compute;\n"
      "      compute = (W + 1) * 2;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(5)::compute();\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(ParameterizedSubroutineSim, ParameterShift) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter W = 0);\n"
      "    static function int shift_up(input int val);\n"
      "      shift_up = val << W;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(3)::shift_up(1);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 8u);
}

TEST(ParameterizedSubroutineSim, ForLoopDifferentSpecs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  virtual class C #(parameter N = 4);\n"
      "    static function int sum_to_n;\n"
      "      sum_to_n = 0;\n"
      "      for (int i = 1; i <= N; i = i + 1)\n"
      "        sum_to_n = sum_to_n + i;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int r3, r4;\n"
      "  initial begin\n"
      "    r3 = C#(3)::sum_to_n();\n"
      "    r4 = C#(4)::sum_to_n();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r3", 6u}, {"r4", 10u}});
}

TEST(ParameterizedSubroutineSim, EncoderDecoderSameClass) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  virtual class C #(parameter DECODE_W = 8,\n"
      "                     parameter ENCODE_W = $clog2(DECODE_W));\n"
      "    static function int ENCODER_f(input int DecodeIn);\n"
      "      ENCODER_f = 0;\n"
      "      for (int i = 0; i < DECODE_W; i = i + 1)\n"
      "        if (DecodeIn & (1 << i))\n"
      "          ENCODER_f = i;\n"
      "    endfunction\n"
      "    static function int DECODER_f(input int EncodeIn);\n"
      "      DECODER_f = 1 << EncodeIn;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int enc_out, dec_out;\n"
      "  initial begin\n"
      "    enc_out = C#(8)::ENCODER_f(64);\n"
      "    dec_out = C#(4)::DECODER_f(3);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"enc_out", 6u}, {"dec_out", 8u}});
}

TEST(ParameterizedSubroutineSim, StaticTaskExecution) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class Logger#(parameter int TAG = 0);\n"
      "    static task set_flag(output int dest);\n"
      "      dest = TAG;\n"
      "    endtask\n"
      "  endclass\n"
      "  int result;\n"
      "  initial Logger#(42)::set_flag(result);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(ParameterizedSubroutineSim, ParamControlsVariableWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class Mask#(parameter W = 4);\n"
      "  static function logic [W-1:0] all_ones;\n"
      "    return '1;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r4, r8;\n"
      "  initial begin\n"
      "    r4 = Mask#(4)::all_ones();\n"
      "    r8 = Mask#(8)::all_ones();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r4", 15u}, {"r8", 255u}});
}

TEST(ParameterizedSubroutineSim, SpecializationArgFromModuleParameter) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  parameter P = 20;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int get_w; get_w = W; endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(P)::get_w();\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(ParameterizedSubroutineSim, SpecializationArgFromLocalparam) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  localparam LW = 12;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int get_w; get_w = W; endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(LW)::get_w();\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(ParameterizedSubroutineSim,
     DISABLED_TheEncoderDecoderExampleDisplaysItsResults) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("virtual class C#(parameter DECODE_W, "
                 "parameter ENCODE_W = $clog2(DECODE_W));\n"
                 "  static function logic [ENCODE_W-1:0] ENCODER_f\n"
                 "      (input logic [DECODE_W-1:0] DecodeIn);\n"
                 "    ENCODER_f = '0;\n"
                 "    for (int i=0; i<DECODE_W; i++) begin\n"
                 "      if (DecodeIn[i]) begin\n"
                 "        ENCODER_f = i[ENCODE_W-1:0];\n"
                 "        break;\n"
                 "      end\n"
                 "    end\n"
                 "  endfunction\n"
                 "  static function logic [DECODE_W-1:0] DECODER_f\n"
                 "      (input logic [ENCODE_W-1:0] EncodeIn);\n"
                 "    DECODER_f = '0;\n"
                 "    DECODER_f[EncodeIn] = 1'b1;\n"
                 "  endfunction\n"
                 "endclass\n"
                 "module top ();\n"
                 "  logic [7:0] encoder_in;\n"
                 "  logic [2:0] encoder_out;\n"
                 "  logic [1:0] decoder_in;\n"
                 "  logic [3:0] decoder_out;\n"
                 "  assign encoder_in = 8'b0100_0000;\n"
                 "  assign decoder_in = 2'b11;\n"
                 "  assign encoder_out = C#(8)::ENCODER_f(encoder_in);\n"
                 "  assign decoder_out = C#(4)::DECODER_f(decoder_in);\n"
                 "  initial begin\n"
                 "    #50;\n"
                 "    $display(\"Encoder input = %b Encoder output = %b\\n\",\n"
                 "      encoder_in, encoder_out );\n"
                 "    $display(\"Decoder input = %b Decoder output = %b\\n\",\n"
                 "      decoder_in, decoder_out );\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "Encoder input = 01000000 Encoder output = 110\n\n"
      "Decoder input = 11 Decoder output = 1000\n\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParameterizedSubroutineSim, EachSpecializationSizesTheArgumentItTakes) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("virtual class C#(parameter W = 8);\n"
                 "  static function int keep(input logic [W-1:0] x);\n"
                 "    return x;\n"
                 "  endfunction\n"
                 "  static task put(input logic [W-1:0] x, "
                 "output int y);\n"
                 "    y = x;\n"
                 "  endtask\n"
                 "endclass\n"
                 "module m;\n"
                 "  int r1, r2;\n"
                 "  initial begin\n"
                 "    C#(4)::put(9'h1ff, r1);\n"
                 "    C#(6)::put(9'h1ff, r2);\n"
                 "    $display(\"%0d %0d %0d %0d\", C#(4)::keep(9'h1ff),\n"
                 "             C#(8)::keep(9'h1ff), r1, r2);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "15 255 15 63\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParameterizedSubroutineSim,
     DISABLED_ATypeParameterSetsTheTypeASubroutineReturns) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("virtual class C#(type T = int);\n"
                 "  static function T conv(input int x);\n"
                 "    return T'(x);\n"
                 "  endfunction\n"
                 "endclass\n"
                 "module m;\n"
                 "  initial $display(\"%0d %0d %0d\", C#(byte)::conv(300),\n"
                 "                   C#(shortint)::conv(70000), "
                 "C#()::conv(70000));\n"
                 "endmodule\n",
                 f),
      "44 4464 70000\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParameterizedSubroutineSim,
     DISABLED_AnEmptySpecializationTakesEveryDefault) {
  SimFixture f;
  EXPECT_EQ(RunCapture("virtual class C#(parameter A = 6, "
                       "parameter B = A * 2);\n"
                       "  static function int sum; return A + B; endfunction\n"
                       "endclass\n"
                       "module m;\n"
                       "  initial $display(\"%0d %0d\", C#()::sum(), "
                       "C#(1)::sum());\n"
                       "endmodule\n",
                       f),
            "18 3\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParameterizedSubroutineSim, AParameterizedSubroutineIsDeclaredInAPackage) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package p;\n"
                 "  virtual class C#(parameter W = 1);\n"
                 "    static function int scale(int x); return x * W; "
                 "endfunction\n"
                 "  endclass\n"
                 "  function int twice_five; return C#(2)::scale(5); "
                 "endfunction\n"
                 "endpackage\n"
                 "module m;\n"
                 "  import p::*;\n"
                 "  initial $display(\"%0d %0d %0d\", p::C#(3)::scale(5),\n"
                 "                   C#(4)::scale(5), twice_five());\n"
                 "endmodule\n",
                 f),
      "15 20 10\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParameterizedSubroutineSim,
     AParameterizedSubroutineIsCalledFromEveryScope) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("virtual class C#(parameter W = 1);\n"
                 "  static function int scale(int x); return x * W; "
                 "endfunction\n"
                 "endclass\n"
                 "class K;\n"
                 "  function int run(int x); return C#(5)::scale(x); "
                 "endfunction\n"
                 "endclass\n"
                 "interface i;\n"
                 "  int r;\n"
                 "  initial r = C#(6)::scale(2);\n"
                 "endinterface\n"
                 "module m;\n"
                 "  function int fn(int x); return C#(7)::scale(x); "
                 "endfunction\n"
                 "  task tk(output int y); y = C#(8)::scale(2); endtask\n"
                 "  K k = new;\n"
                 "  i u();\n"
                 "  int a, g;\n"
                 "  if (1) begin : gb\n"
                 "    int r;\n"
                 "    initial r = C#(9)::scale(2);\n"
                 "  end\n"
                 "  initial begin\n"
                 "    tk(a);\n"
                 "    #1 $display(\"%0d %0d %0d %0d %0d\", k.run(2), u.r, "
                 "fn(2), a, gb.r);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "10 12 14 16 18\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParameterizedSubroutineSim, AParameterizedSubroutineIsCalledInAProgram) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program q;\n"
                       "  virtual class C#(parameter W = 1);\n"
                       "    static function int scale(int x); return x * W; "
                       "endfunction\n"
                       "  endclass\n"
                       "  initial $display(\"%0d\", C#(11)::scale(3));\n"
                       "endprogram\n",
                       f),
            "33\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParameterizedSubroutineSim, AStaticTaskWaitsForItsSpecializationsDelay) {
  SimFixture f;
  EXPECT_EQ(RunCapture("virtual class C#(parameter D = 1);\n"
                       "  static task pause; #D; endtask\n"
                       "endclass\n"
                       "module m;\n"
                       "  initial begin\n"
                       "    C#(3)::pause();\n"
                       "    $display(\"%0t\", $time);\n"
                       "    C#(4)::pause();\n"
                       "    $display(\"%0t\", $time);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3\n7\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
