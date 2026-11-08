#include <gtest/gtest.h>

#include <cstdint>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(FunctionReturnSim, VoidFunctionReturnsZero) {
  FuncFixture f;

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "set_val";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {
      {Direction::kInput, false, false, false, {}, "a", nullptr, {}}};
  f.ctx.RegisterFunction("set_val", func);

  auto* call = MakeCall(f.arena, "set_val", {MakeInt(f.arena, 42)});
  auto result = EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(FunctionReturnSim, ReturnStatementFromFunction) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function int get_val();\n"
      "    return 42;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = get_val();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(FunctionReturnSim, FunctionReturnValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] add_one(input logic [7:0] v);\n"
      "    return v + 8'd1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = add_one(8'd9);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(FunctionReturnSim, NestedFunctionCalls) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function logic [7:0] double_val(input logic [7:0] v);\n"
      "    return v * 8'd2;\n"
      "  endfunction\n"
      "  function logic [7:0] quad_val(input logic [7:0] v);\n"
      "    return double_val(double_val(v));\n"
      "  endfunction\n"
      "  initial x = quad_val(8'd3);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(FunctionReturnSim, FunctionNameAssignReturnsValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  function logic [15:0] myfunc1(input logic [7:0] a, input logic [7:0] "
      "b);\n"
      "    myfunc1 = a * b - 16'd1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = myfunc1(8'd3, 8'd5);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 14u}});
}

TEST(FunctionReturnSim, ReturnOverridesFunctionNameAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function int compute();\n"
      "    compute = 100;\n"
      "    return 42;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = compute();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 42u}});
}

TEST(FunctionReturnSim, EmptyFunctionReturnsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function int nop();\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = nop();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0u}});
}

TEST(FunctionReturnSim, FunctionNameAssignConditional) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function int abs_val(input int v);\n"
      "    if (v < 0)\n"
      "      abs_val = -v;\n"
      "    else\n"
      "      abs_val = v;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = abs_val(32'd7);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 7u}});
}

TEST(FunctionReturnSim, NonvoidFunctionAsOperandInExpr) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function logic [31:0] five; return 32'd5; endfunction\n"
      "  initial x = five() + 32'd3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 8u);
}

TEST(FunctionReturnSim, VoidFunctionSideEffect) {
  FuncFixture f;

  auto* g_var = f.ctx.CreateVariable("g", 32);
  g_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "store";
  func->return_type.kind = DataTypeKind::kVoid;
  func->func_args = {
      {Direction::kOutput, false, false, false, {}, "out", nullptr, {}}};
  func->func_body_stmts.push_back(
      MakeAssign(f.arena, "out", MakeInt(f.arena, 99)));
  f.ctx.RegisterFunction("store", func);

  auto* call = MakeCall(f.arena, "store", {MakeId(f.arena, "g")});
  EvalExpr(call, f.ctx, f.arena);

  EXPECT_EQ(g_var->value.ToUint64(), 99u);
}

TEST(FunctionReturnSim, VoidFunctionBareReturnExitsEarly) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function void set_x(output logic [31:0] v);\n"
      "    v = 32'd10;\n"
      "    return;\n"
      "    v = 32'd99;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    set_x(x);\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 10u);
}

TEST(FunctionReturnSim, BareReturnUsesImplicitVar) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function int compute(input int a);\n"
      "    compute = a * 3;\n"
      "    return;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = compute(5);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 15u}});
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return statement in non-void function 'compute' "
                            "gives no value to return",
                            5, "12.8"));
}

TEST(FunctionReturnSim, MultipleFunctionNameAssignsLastWins) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function int pick();\n"
      "    pick = 32'd1;\n"
      "    pick = 32'd2;\n"
      "    pick = 32'd3;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = pick();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 3u}});
}

TEST(FunctionReturnSim, FunctionNameAssignRespectsReturnWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] x;\n"
      "  function logic [3:0] narrow();\n"
      "    narrow = 8'hFF;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = narrow();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 15u}});
}

TEST(FunctionReturnSim, SystemFunctionAsImplicitVariableInExpression) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = $unsigned(32'd42) + 32'd1;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 43u);
}

TEST(FunctionReturnSim, BuiltinMethodCallAsImplicitVariableInExpression) {
  uint64_t r = RunAndGet(
      "module t;\n"
      "  int q[$];\n"
      "  int r;\n"
      "  initial begin\n"
      "    q.push_back(10);\n"
      "    q.push_back(20);\n"
      "    r = q.size() + 5;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(r, 7u);
}

TEST(FunctionReturnSim, ReturnValueTakesTheDeclaredWidthOfTheFunction) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  function logic [7:0] low();\n"
      "    return 16'h134;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = low();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x34u);
}

TEST(FunctionReturnSim, ReturnOfUnsignedBitZeroExtendsIntoSignedReturnType) {
  uint64_t r = RunAndGet(
      "module t;\n"
      "  int r;\n"
      "  function int same(int a, int b);\n"
      "    return (a == b);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    r = same(5, 5);\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(r, 1u);
}

TEST(FunctionReturnSim, TypedefReturnTypeSizesTheImplicitVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef bit [3:0] nib;\n"
      "  logic [7:0] x;\n"
      "  function nib get_nib();\n"
      "    return 8'hFF;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = get_nib();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(FunctionReturnSim, TypedefReturnTypeWiderThanTheFallbackKeepsItsHighBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef bit [39:0] wide;\n"
      "  logic [39:0] x;\n"
      "  function wide get_wide();\n"
      "    return 40'hAA_AAAA_AAAA;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = get_wide();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAAAAAAAAAAull);
}

TEST(FunctionReturnSim, TwoStateLocalCopyLeavesTheSourceUnknownsIntact) {
  SimFixture f;
  auto* read_var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  bit [7:0] y;\n"
      "  function void take();\n"
      "    y = x;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 8'b1100xx01;\n"
      "    take();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(read_var, nullptr);
  auto* written_var = f.ctx.FindVariable("y");
  ASSERT_NE(written_var, nullptr);
  EXPECT_EQ(read_var->value.words[0].aval & 0xFFu, 0xCDu);
  EXPECT_EQ(read_var->value.words[0].bval & 0xFFu, 0x0Cu);
  EXPECT_EQ(written_var->value.words[0].aval & 0xFFu, 0xC1u);
  EXPECT_EQ(written_var->value.words[0].bval & 0xFFu, 0x00u);
}

TEST(FunctionReturnSim, TaskBodyCopyRunsOnTheOrdinaryStatementExecutor) {
  SimFixture f;
  auto* source = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] p;\n"
      "  bit [7:0] q;\n"
      "  task grab();\n"
      "    q = p;\n"
      "  endtask\n"
      "  initial begin\n"
      "    p = 8'b0110x1x0;\n"
      "    grab();\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(source, nullptr);
  auto* target = f.ctx.FindVariable("q");
  ASSERT_NE(target, nullptr);
  EXPECT_EQ(source->value.words[0].aval & 0xFFu, 0x6Eu);
  EXPECT_EQ(source->value.words[0].bval & 0xFFu, 0x0Au);
  EXPECT_EQ(target->value.words[0].aval & 0xFFu, 0x64u);
  EXPECT_EQ(target->value.words[0].bval & 0xFFu, 0x00u);
}

TEST(FunctionReturnSim, MemberDepositAfterABodyCopyLeavesTheSourceIntact) {
  SimFixture f;
  auto* origin = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t a;\n"
      "  pair_t b;\n"
      "  function void split();\n"
      "    b = a;\n"
      "    b.lo = 8'h00;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a.hi = 8'h5A;\n"
      "    a.lo = 8'hC3;\n"
      "    split();\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(origin, nullptr);
  auto* duplicate = f.ctx.FindVariable("b");
  ASSERT_NE(duplicate, nullptr);
  EXPECT_EQ(origin->value.ToUint64(), 0x5AC3u);
  EXPECT_EQ(duplicate->value.ToUint64(), 0x5A00u);
}

TEST(FunctionReturnSim, ReturnIntoATwoStateResultKeepsTheReadVariableUnknown) {
  SimFixture f;
  auto* source = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] pattern;\n"
      "  logic [7:0] result;\n"
      "  function bit [7:0] fetch();\n"
      "    return pattern;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    pattern = 8'b1x01101x;\n"
      "    result = fetch();\n"
      "  end\n"
      "endmodule\n",
      f, "pattern");
  ASSERT_NE(source, nullptr);
  auto* returned = f.ctx.FindVariable("result");
  ASSERT_NE(returned, nullptr);
  EXPECT_EQ(source->value.words[0].aval & 0xFFu, 0xDBu);
  EXPECT_EQ(source->value.words[0].bval & 0xFFu, 0x41u);
  EXPECT_EQ(returned->value.words[0].aval & 0xFFu, 0x9Au);
  EXPECT_EQ(returned->value.words[0].bval & 0xFFu, 0x00u);
}

TEST(FunctionReturnSim, ReturnOfAnInoutFormalLeavesTheCallersActualIntact) {
  SimFixture f;
  auto* actual = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] held;\n"
      "  logic [7:0] copy;\n"
      "  function bit [7:0] relay(inout logic [7:0] io);\n"
      "    return io;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    held = 8'bx11001x1;\n"
      "    copy = relay(held);\n"
      "  end\n"
      "endmodule\n",
      f, "held");
  ASSERT_NE(actual, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* taken_out = f.ctx.FindVariable("copy");
  ASSERT_NE(taken_out, nullptr);
  EXPECT_EQ(actual->value.words[0].aval & 0xFFu, 0xE7u);
  EXPECT_EQ(actual->value.words[0].bval & 0xFFu, 0x82u);
  EXPECT_EQ(taken_out->value.words[0].aval & 0xFFu, 0x65u);
  EXPECT_EQ(taken_out->value.words[0].bval & 0xFFu, 0x00u);
}

TEST(FunctionReturnSim, FunctionNameAssignOfAVariableCoercesOnlyTheResult) {
  SimFixture f;
  auto* kept = RunAndFindVar(
      "module t;\n"
      "  logic [11:0] stored;\n"
      "  logic [11:0] taken;\n"
      "  function bit [11:0] grab_bits();\n"
      "    grab_bits = stored;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    stored = 12'b1010x0111x01;\n"
      "    taken = grab_bits();\n"
      "  end\n"
      "endmodule\n",
      f, "stored");
  ASSERT_NE(kept, nullptr);
  auto* handed_back = f.ctx.FindVariable("taken");
  ASSERT_NE(handed_back, nullptr);
  EXPECT_EQ(kept->value.words[0].aval & 0xFFFu, 0xABDu);
  EXPECT_EQ(kept->value.words[0].bval & 0xFFFu, 0x084u);
  EXPECT_EQ(handed_back->value.words[0].aval & 0xFFFu, 0xA39u);
  EXPECT_EQ(handed_back->value.words[0].bval & 0xFFFu, 0x000u);
}

TEST(FunctionReturnSim,
     MemberWritesThroughTheFunctionNameFillAnUnpackedStruct) {
  SimFixture f;
  auto* got = RunAndFindVar(
      "module t;\n"
      "  typedef struct { int a; int b; } st_t;\n"
      "  function st_t mk();\n"
      "    mk.a = 3;\n"
      "    mk.b = 4;\n"
      "  endfunction\n"
      "  st_t r;\n"
      "  int got;\n"
      "  initial begin\n"
      "    r = mk();\n"
      "    got = r.a * 10 + r.b;\n"
      "  end\n"
      "endmodule\n",
      f, "got");
  ASSERT_NE(got, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(got->value.ToUint64(), 34u);
}

TEST(FunctionReturnSim, MemberWritesThroughTheFunctionNameFillAPackedStruct) {
  SimFixture f;
  auto* got = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { int a; int b; } st_t;\n"
      "  function st_t mk();\n"
      "    mk.a = 3;\n"
      "    mk.b = 4;\n"
      "  endfunction\n"
      "  st_t r;\n"
      "  int got;\n"
      "  initial begin\n"
      "    r = mk();\n"
      "    got = r.a * 10 + r.b;\n"
      "  end\n"
      "endmodule\n",
      f, "got");
  ASSERT_NE(got, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(got->value.ToUint64(), 34u);
}

TEST(FunctionReturnSim, ReturnOfTheFunctionNameCarriesItsWrittenMembers) {
  SimFixture f;
  auto* got = RunAndFindVar(
      "module t;\n"
      "  typedef struct { int a; int b; } st_t;\n"
      "  function st_t mk();\n"
      "    mk.a = 5;\n"
      "    mk.b = mk.a + 2;\n"
      "    return mk;\n"
      "  endfunction\n"
      "  st_t r;\n"
      "  int got;\n"
      "  initial begin\n"
      "    r = mk();\n"
      "    got = r.a * 10 + r.b;\n"
      "  end\n"
      "endmodule\n",
      f, "got");
  ASSERT_NE(got, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(got->value.ToUint64(), 57u);
}

TEST(FunctionReturnSim, SizeOfAQueueACallReturned) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef int iq_t[$];\n"
      "  function automatic iq_t fq();\n"
      "    iq_t q;\n"
      "    q.push_back(10);\n"
      "    q.push_back(20);\n"
      "    q.push_back(30);\n"
      "    return q;\n"
      "  endfunction\n"
      "  int got;\n"
      "  initial got = fq().size();\n"
      "endmodule\n",
      "got");
  EXPECT_EQ(v, 3u);
}

TEST(FunctionReturnSim, IndexOfAQueueACallReturned) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef int iq_t[$];\n"
      "  function automatic iq_t fq();\n"
      "    iq_t q;\n"
      "    q.push_back(10);\n"
      "    q.push_back(20);\n"
      "    q.push_back(30);\n"
      "    return q;\n"
      "  endfunction\n"
      "  int got;\n"
      "  initial got = fq()[1];\n"
      "endmodule\n",
      "got");
  EXPECT_EQ(v, 20u);
}

TEST(FunctionReturnSim, SizeAndIndexOfADynamicArrayACallReturned) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef int ida_t[];\n"
      "  int d[];\n"
      "  function ida_t fd();\n"
      "    d = new[2];\n"
      "    d[1] = 7;\n"
      "    return d;\n"
      "  endfunction\n"
      "  int got;\n"
      "  initial got = fd().size() * 10 + fd()[1];\n"
      "endmodule\n",
      "got");
  EXPECT_EQ(v, 27u);
}

TEST(FunctionReturnSim, IndexOfAFixedArrayACallReturned) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef int ia_t[3];\n"
      "  function automatic ia_t fa();\n"
      "    ia_t a;\n"
      "    a[0] = 10;\n"
      "    a[1] = 20;\n"
      "    a[2] = 30;\n"
      "    return a;\n"
      "  endfunction\n"
      "  int got;\n"
      "  initial got = fa()[1] * 100 + fa()[2];\n"
      "endmodule\n",
      "got");
  EXPECT_EQ(v, 2030u);
}

TEST(FunctionReturnSim, MemberOfAnUnpackedStructACallReturned) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct { int a; int b; } st_t;\n"
      "  function st_t mk();\n"
      "    mk.a = 3;\n"
      "    mk.b = 4;\n"
      "  endfunction\n"
      "  int got;\n"
      "  initial got = mk().a * 10 + mk().b;\n"
      "endmodule\n",
      "got");
  EXPECT_EQ(v, 34u);
}

TEST(FunctionReturnSim, MemberOfAPackedStructACallReturned) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { int a; int b; } st_t;\n"
      "  function st_t mk();\n"
      "    mk.a = 3;\n"
      "    mk.b = 4;\n"
      "  endfunction\n"
      "  int got;\n"
      "  initial got = mk().a * 10 + mk().b;\n"
      "endmodule\n",
      "got");
  EXPECT_EQ(v, 34u);
}

}  // namespace
