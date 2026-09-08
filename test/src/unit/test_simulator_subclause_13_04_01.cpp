#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
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

// §13.4.1: unless otherwise specified, all nonvoid function calls -- including
// built-in methods -- may be used as an implicit variable within an expression.
// Here the built-in queue method size() is a nonvoid call embedded in an
// arithmetic expression, and the whole expression evaluates end to end.
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

// §13.4.1: the implicitly declared internal variable "has the same type as
// the function return value", so a `return` of a wider expression is an
// assignment to that variable rather than a replacement of it, and the caller
// sees the declared eight bits. The value returned here needs nine to survive
// whole, so a result that kept the expression's own width would read 0x134.
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

// §13.4.1 x §10.7: the same assignment widens a narrower expression, and §10.7
// extends it by the expression's own signedness rather than the variable's. A
// comparison yields one unsigned bit, so an `int` function returning one hands
// the caller 1 -- sign-extending that bit to the declared thirty-two would give
// -1, which is what an assignment carrying the variable's signedness into the
// extension produces.
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

// §13.4.1: the function definition implicitly declares a variable with the same
// type as the function return value, and Syntax 6-4 makes a type_identifier a
// data_type like any other, so a function declared to return `nib` returns the
// four bits `nib` names. Returning 8'hFF through it gives 15; a return type the
// simulator cannot size falls back to 32 bits and would give 255. A typedef of
// exactly 32 bits would make the two answers coincide and prove nothing.
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

// §13.4.1 again, on a typedef wider than the 32-bit fallback rather than
// narrower: the fallback is not merely imprecise but too small, and every bit
// above the first word is lost. 40'hAA_AAAA_AAAA truncated to 32 bits reads
// 0xAAAAAAAA, so the high byte is what the case turns on.
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

// §13.4.1's implicitly declared variable is one storage element, and §6.8 makes
// every other declaration one of its own: "A variable is an abstraction of a
// data storage element. A variable shall store a value from one assignment to
// the next." A statement in a function body that only reads `x` therefore
// cannot change what `x` stores, whatever it does to its own target.
//
// A subroutine body runs on its own statement executor -- a void function
// called with parentheses is declined by SetupTaskCall and reaches
// ExecFunctionBody, so `take()` lands in ExecFuncIdentifierAssign rather than
// in the executor an initial block uses. That executor stored the evaluated
// right-hand value straight into the target, and a Logic4Vec copies its `words`
// pointer rather than the words: with the resize declining to build anything at
// equal widths, `y` was left naming `x`'s storage. The line after the store
// coerces a 2-state target in place -- §6.11.2: "any unknown or high-impedance
// bits shall be converted to zeros" -- and the coercion travelled back through
// that alias to clear the unknowns of `x`, in the statement that only read it.
//
// The eight bits on each side are load-bearing. Unequal widths make the
// assignment resize, which builds the value in a fresh store and hides the
// sharing; matching widths are what let the read value reach the target
// unresized.
//
// The assertions read words[0] because ToUint64 projects aval & ~bval: an x bit
// already reads 0 there, so `x` answers 0xC1 through it whether its unknowns
// survived or not. 8'b1100xx01 is stored as aval 0xCD with bval 0x0C, an x bit
// being aval 1 with bval 1; clearing those unknowns gives aval 0xC1 with bval
// 0x00, which is what `y` alone is entitled to hold.
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

// The contrast, and the reason the case above is written as a function. §13.4
// and §13.3 give a task and a function the same procedural body, but the two
// calls are routed apart: a task called with parentheses is claimed by
// SetupTaskCall, and ExecInlineTaskCall then walks its body through ExecStmt,
// so `q = p` written in a task is executed by the ordinary blocking-assignment
// path -- the one that takes its own copy of the right-hand words before any
// store can see them. Only the void function above is declined by SetupTaskCall
// and reaches the subroutine-body executor.
//
// So this case states the boundary of the claim rather than one more way to
// break it: it holds on either side of the fix the function case asks for, and
// what it discriminates against is a task body rerouted onto the
// subroutine-body executor, which would carry that executor's in-place coercion
// back into `p`.
//
// 8'b0110x1x0 is stored as aval 0x6E with bval 0x0A, and the 2-state copy of it
// is aval 0x64 with bval 0x00 -- a different pattern from the function case, so
// the two state their claim on different bits.
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

// The same §6.8 independence of storage elements, reached through a write that
// lands after the copy rather than inside it, and with no 2-state coercion
// anywhere in it. §7.2.1 makes a packed struct "a single vector", so assigning
// one of its members deposits into a window of the whole struct's storage,
// writing through the words the struct already holds. A target left naming its
// source's storage therefore takes every later member write to the target back
// to the source, which records an assignment it never received.
//
// Both statements sit in the function body, so the copy and the deposit are
// both executed by the subroutine-body executor. A packed struct lays its first
// member at the high bits, so `a.hi = 8'h5A; a.lo = 8'hC3;` stores 16'h5AC3,
// `hi` occupying bits [15:8] and `lo` bits [7:0]. `b = a` must give `b` its own
// 16'h5AC3, and depositing 8'h00 over `b.lo` then clears bits [7:0] of `b`
// alone: `b` reads 16'h5A00 and `a` is still 16'h5AC3. Shared storage answers
// 16'h5A00 for both, `a` having lost the 8'hC3 it was assigned and never
// overwrote.
//
// Every bit involved is known, so ToUint64 reports the stored value exactly and
// its projection hides nothing here. The two structs are sixteen bits each,
// which is again what keeps the copy from resizing into a fresh store and so
// from hiding the sharing.
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

}  // namespace
