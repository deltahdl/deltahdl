#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

static Variable* RunAndFind(const std::string& src, SimFixture& f,
                            const char* var_name) {
  auto* design = ElaborateSrc(src, f);
  if (!design) return nullptr;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return f.ctx.FindVariable(var_name);
}

TEST(SimCh13, VirtualClassIsAbstract) {
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

TEST(SimCh13, ClassParamsPreserved) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class C #(parameter A = 1, parameter B = 2);\n"
      "    static function int f; f = A; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* info = f.ctx.FindClassType("C");
  ASSERT_NE(info, nullptr);
  ASSERT_NE(info->decl, nullptr);
  EXPECT_EQ(info->decl->params.size(), 2u);
  EXPECT_EQ(info->decl->params[0].first, "A");
  EXPECT_EQ(info->decl->params[1].first, "B");
}

TEST(SimCh13, StaticMethodRegistered) {
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
  EXPECT_TRUE(it->second->is_static);
}

TEST(SimCh13, MultipleStaticMethodsRegistered) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int alpha; alpha = W; endfunction\n"
      "    static function int beta; beta = W + 1; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  auto* info = f.ctx.FindClassType("C");
  ASSERT_NE(info, nullptr);
  EXPECT_NE(info->methods.find("alpha"), info->methods.end());
  EXPECT_NE(info->methods.find("beta"), info->methods.end());
}

TEST(SimCh13, NonVirtualParameterizedClass) {
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

TEST(SimCh13, SimpleParameterReturn) {
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

TEST(SimCh13, DefaultParameterValue) {
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

TEST(SimCh13, DefaultParamClog2) {
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

TEST(SimCh13, MultipleSpecializations) {
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
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r1 = f.ctx.FindVariable("r1");
  auto* r2 = f.ctx.FindVariable("r2");
  ASSERT_NE(r1, nullptr);
  ASSERT_NE(r2, nullptr);
  EXPECT_EQ(r1->value.ToUint64(), 8u);
  EXPECT_EQ(r2->value.ToUint64(), 32u);
}

TEST(SimCh13, TwoParametersExplicit) {
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

TEST(SimCh13, ParameterArithmetic) {
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

TEST(SimCh13, ParameterBitmask) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int mask;\n"
      "      mask = (1 << W) - 1;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(4)::mask();\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(SimCh13, ParameterIfElse) {
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

TEST(SimCh13, MethodWithInputArg) {
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

TEST(SimCh13, MethodWithTwoArgs) {
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

TEST(SimCh13, TwoMethodsSameClass) {
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
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r1 = f.ctx.FindVariable("r1");
  auto* r2 = f.ctx.FindVariable("r2");
  ASSERT_NE(r1, nullptr);
  ASSERT_NE(r2, nullptr);
  EXPECT_EQ(r1->value.ToUint64(), 10u);
  EXPECT_EQ(r2->value.ToUint64(), 11u);
}

TEST(SimCh13, ContinuousAssignCall) {
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

TEST(SimCh13, AlwaysCombCall) {
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

TEST(SimCh13, DifferentSpecsDifferentResults) {
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
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r4 = f.ctx.FindVariable("r4");
  auto* r8 = f.ctx.FindVariable("r8");
  ASSERT_NE(r4, nullptr);
  ASSERT_NE(r8, nullptr);
  EXPECT_EQ(r4->value.ToUint64(), 15u);
  EXPECT_EQ(r8->value.ToUint64(), 255u);
}

TEST(SimCh13, ParameterSubtract) {
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

TEST(SimCh13, ChainedParamExpr) {
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

TEST(SimCh13, ParameterShift) {
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

TEST(SimCh13, MultipleCallsSameSpec) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  virtual class C #(parameter W = 0);\n"
      "    static function int add_w(input int x);\n"
      "      add_w = x + W;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = C#(10)::add_w(1);\n"
      "    r2 = C#(10)::add_w(2);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r1 = f.ctx.FindVariable("r1");
  auto* r2 = f.ctx.FindVariable("r2");
  ASSERT_NE(r1, nullptr);
  ASSERT_NE(r2, nullptr);
  EXPECT_EQ(r1->value.ToUint64(), 11u);
  EXPECT_EQ(r2->value.ToUint64(), 12u);
}

TEST(SimCh13, ZeroParamValue) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter W = 8);\n"
      "    static function int get_w; get_w = W; endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(0)::get_w();\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(SimCh13, ParameterNestedIf) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter W = 0);\n"
      "    static function int encode_size;\n"
      "      if (W <= 8)\n"
      "        encode_size = 1;\n"
      "      else if (W <= 16)\n"
      "        encode_size = 2;\n"
      "      else if (W <= 32)\n"
      "        encode_size = 4;\n"
      "      else\n"
      "        encode_size = 8;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(24)::encode_size();\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(SimCh13, ForLoopWithParam) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter N = 4);\n"
      "    static function int sum_to_n;\n"
      "      sum_to_n = 0;\n"
      "      for (int i = 1; i <= N; i = i + 1)\n"
      "        sum_to_n = sum_to_n + i;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(5)::sum_to_n();\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(SimCh13, ForLoopDifferentSpecs) {
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
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r3 = f.ctx.FindVariable("r3");
  auto* r4 = f.ctx.FindVariable("r4");
  ASSERT_NE(r3, nullptr);
  ASSERT_NE(r4, nullptr);
  EXPECT_EQ(r3->value.ToUint64(), 6u);
  EXPECT_EQ(r4->value.ToUint64(), 10u);
}

TEST(SimCh13, DecoderFunction) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter DECODE_W = 4,\n"
      "                     parameter ENCODE_W = $clog2(DECODE_W));\n"
      "    static function int DECODER_f(input int EncodeIn);\n"
      "      DECODER_f = 0;\n"
      "      DECODER_f = DECODER_f | (1 << EncodeIn);\n"
      "    endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  initial result = C#(4)::DECODER_f(3);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 8u);
}

TEST(SimCh13, EncoderFunction) {
  SimFixture f;
  auto* var = RunAndFind(
      "module t;\n"
      "  virtual class C #(parameter DECODE_W = 8,\n"
      "                     parameter ENCODE_W = $clog2(DECODE_W));\n"
      "    static function int ENCODER_f(input int DecodeIn);\n"
      "      ENCODER_f = 0;\n"
      "      for (int i = 0; i < DECODE_W; i = i + 1)\n"
      "        if (DecodeIn & (1 << i))\n"
      "          ENCODER_f = i;\n"
      "    endfunction\n"
      "  endclass\n"
      "  int result;\n"
      "  // Encode bit 6: 8'b0100_0000 = 64.\n"
      "  initial result = C#(8)::ENCODER_f(64);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(SimCh13, EncoderDecoderSameClass) {
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
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* enc = f.ctx.FindVariable("enc_out");
  auto* dec = f.ctx.FindVariable("dec_out");
  ASSERT_NE(enc, nullptr);
  ASSERT_NE(dec, nullptr);
  EXPECT_EQ(enc->value.ToUint64(), 6u);
  EXPECT_EQ(dec->value.ToUint64(), 8u);
}

TEST(SimCh13, ParserPreservesParams) {
  SimFixture f;
  auto fid = f.mgr.AddFile("<test>",
                           "module t;\n"
                           "  class C #(parameter W = 8);\n"
                           "    static function int f; f = W; endfunction\n"
                           "  endclass\n"
                           "  int x;\n"
                           "  initial x = C#(16)::f();\n"
                           "endmodule\n");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(cu->modules.empty());

}
