#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/class_object.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

// =============================================================================
// Full-simulation fixture: parse → elaborate → lower → run → check.
// =============================================================================

struct SimCh13Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimCh13Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// Helper: elaborate + lower + run, then return FindVariable result.
static Variable* RunAndFind(const std::string& src, SimCh13Fixture& f,
                            const char* var_name) {
  auto* design = ElaborateSrc(src, f);
  if (!design) return nullptr;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return f.ctx.FindVariable(var_name);
}

// =============================================================================
// §13.8: ClassTypeInfo-level tests — verify that the lowerer correctly
// registers parameterized virtual classes with static methods.
// =============================================================================

// §13.8: Virtual class flag maps to is_abstract in ClassTypeInfo.
TEST(SimCh13, VirtualClassIsAbstract) {
  SimCh13Fixture f;
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

// §13.8: ClassTypeInfo preserves ClassDecl with params.
TEST(SimCh13, ClassParamsPreserved) {
  SimCh13Fixture f;
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

// §13.8: Static method is registered in ClassTypeInfo.methods.
TEST(SimCh13, StaticMethodRegistered) {
  SimCh13Fixture f;
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

// §13.8: Multiple static methods registered in same class.
TEST(SimCh13, MultipleStaticMethodsRegistered) {
  SimCh13Fixture f;
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

// §13.8: Non-virtual parameterized class also works.
TEST(SimCh13, NonVirtualParameterizedClass) {
  SimCh13Fixture f;
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

// =============================================================================
// §13.8: End-to-end simulation — parameterized scope call C#(N)::method().
// =============================================================================

// §13.8: Static method returns parameter value via C#(16)::get_w().
TEST(SimCh13, SimpleParameterReturn) {
  SimCh13Fixture f;
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

// §13.8: Default parameter used when only first param specified.
TEST(SimCh13, DefaultParameterValue) {
  SimCh13Fixture f;
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
  // Only A=20 specified; B defaults to 5.
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// §13.8: Default parameter using $clog2 of another parameter.
TEST(SimCh13, DefaultParamClog2) {
  SimCh13Fixture f;
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
  // $clog2(8) = 3.
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// §13.8: Multiple specializations in same module give different results.
TEST(SimCh13, MultipleSpecializations) {
  SimCh13Fixture f;
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

// §13.8: Two parameters, both provided explicitly at call site.
TEST(SimCh13, TwoParametersExplicit) {
  SimCh13Fixture f;
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

// §13.8: Parameter used in arithmetic expression.
TEST(SimCh13, ParameterArithmetic) {
  SimCh13Fixture f;
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

// §13.8: Parameter used in bitmask computation: (1 << W) - 1.
TEST(SimCh13, ParameterBitmask) {
  SimCh13Fixture f;
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
  // (1 << 4) - 1 = 15.
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

// §13.8: Parameter in if-else condition.
TEST(SimCh13, ParameterIfElse) {
  SimCh13Fixture f;
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

// §13.8: Static method with input argument.
TEST(SimCh13, MethodWithInputArg) {
  SimCh13Fixture f;
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
  // 5 + 10 = 15.
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

// §13.8: Static method with two input arguments.
TEST(SimCh13, MethodWithTwoArgs) {
  SimCh13Fixture f;
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
  // 4 * 3 + 5 = 17.
  EXPECT_EQ(var->value.ToUint64(), 17u);
}

// §13.8: Two different static methods in same class.
TEST(SimCh13, TwoMethodsSameClass) {
  SimCh13Fixture f;
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

// §13.8: Parameterized scope call in continuous assignment.
TEST(SimCh13, ContinuousAssignCall) {
  SimCh13Fixture f;
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

// §13.8: Parameterized scope call in always_comb.
TEST(SimCh13, AlwaysCombCall) {
  SimCh13Fixture f;
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

// §13.8: Different specializations produce different results.
TEST(SimCh13, DifferentSpecsDifferentResults) {
  SimCh13Fixture f;
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
  EXPECT_EQ(r4->value.ToUint64(), 15u);   // (1<<4)-1
  EXPECT_EQ(r8->value.ToUint64(), 255u);  // (1<<8)-1
}

// §13.8: Parameter subtraction.
TEST(SimCh13, ParameterSubtract) {
  SimCh13Fixture f;
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

// §13.8: Chained parameter expression: (W + 1) * 2.
TEST(SimCh13, ChainedParamExpr) {
  SimCh13Fixture f;
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
  // (5 + 1) * 2 = 12.
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

// §13.8: Parameter used in shift: val << W.
TEST(SimCh13, ParameterShift) {
  SimCh13Fixture f;
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
  // 1 << 3 = 8.
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

// §13.8: Calling same method twice with same specialization.
TEST(SimCh13, MultipleCallsSameSpec) {
  SimCh13Fixture f;
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

// §13.8: Zero parameter value edge case.
TEST(SimCh13, ZeroParamValue) {
  SimCh13Fixture f;
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

// §13.8: Nested if using parameter in static method.
TEST(SimCh13, ParameterNestedIf) {
  SimCh13Fixture f;
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
  // 24 <= 32, so result = 4.
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

// §13.8: For loop in static method with parameter as bound.
TEST(SimCh13, ForLoopWithParam) {
  SimCh13Fixture f;
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
  // 1+2+3+4+5 = 15.
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

// §13.8: For loop with different specializations.
TEST(SimCh13, ForLoopDifferentSpecs) {
  SimCh13Fixture f;
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
  EXPECT_EQ(r3->value.ToUint64(), 6u);   // 1+2+3
  EXPECT_EQ(r4->value.ToUint64(), 10u);  // 1+2+3+4
}

// §13.8 LRM example: Decoder function — C#(4)::DECODER_f(2'b11).
// DECODER_f sets bit EncodeIn to 1: result[3] = 1 → 4'b1000 = 8.
TEST(SimCh13, DecoderFunction) {
  SimCh13Fixture f;
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
  // 1 << 3 = 8 (bit 3 set).
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

// §13.8 LRM example: Encoder function (simplified, no break).
// Finds the last set bit in DecodeIn using a for loop bounded by DECODE_W.
TEST(SimCh13, EncoderFunction) {
  SimCh13Fixture f;
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
  // Bit 6 is set, so encoder returns 6.
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

// §13.8 LRM example: Both encoder and decoder in same class.
TEST(SimCh13, EncoderDecoderSameClass) {
  SimCh13Fixture f;
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
  EXPECT_EQ(enc->value.ToUint64(), 6u);  // bit 6 of 64
  EXPECT_EQ(dec->value.ToUint64(), 8u);  // 1 << 3
}

// §13.8: Parser preserves param expressions in AST (kIdentifier.elements).
TEST(SimCh13, ParserPreservesParams) {
  SimCh13Fixture f;
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
  // Parse succeeds — the parameterized scope expression was accepted.
}
