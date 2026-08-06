#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Returns the resolved value of the named parameter/localparam in the single
// elaborated top module, or -1 if it is absent or was left unresolved. Used to
// observe that a constant function CALL was actually folded at elaboration
// (§13.4.3), not merely accepted without error.
int64_t ResolvedParam(RtlirDesign* design, std::string_view name) {
  if (!design || design->top_modules.empty()) return -1;
  for (const auto& p : design->top_modules[0]->params) {
    if (p.name == name) return p.is_resolved ? p.resolved_value : -1;
  }
  return -1;
}

TEST(ConstantFunctionRulesElaboration, InputOnlyArgOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int double_val(input int n); return n * 2; endfunction\n"
      "  localparam int P = double_val(4);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, OutputArgError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int bad_func(output int n);\n"
      "    n = 0;\n"
      "    return 1;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, InoutArgError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int bad_func(inout int n);\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, RefArgError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int bad_func(ref int n);\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, ForkStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int bad_func(int n);\n"
      "    fork\n"
      "    join_none\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ConstantFunctionElaboration, CallInParameterDecl) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int eight(); return 8; endfunction\n"
      "  parameter P = eight();\n"
      "  logic [P-1:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionElaboration, CallInParameterPortDefault) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int P = calc(4));\n"
      "  function int calc(int n); return n * 2; endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionElaboration, NoArgsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int forty_two(); return 42; endfunction\n"
      "  localparam int P = forty_two();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionElaboration, CallInSubExpressionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int calc(int n); return n * 2; endfunction\n"
      "  localparam int P = calc(4) + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, NonblockingAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int bad_func(int n);\n"
      "    int tmp;\n"
      "    tmp <= n;\n"
      "    return tmp;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ConstantFunctionElaboration, ValidCallInGenerateConditionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int is_wide(int n); return n > 8; endfunction\n"
      "  if (is_wide(16)) begin : g\n"
      "    logic x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstantFunctionRulesElaboration, NonConstantContextOutputArgOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int func_with_output(output int n);\n"
      "    n = 42;\n"
      "    return 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.4.3 (g): a constant function may only call system functions admissible
// in a constant_expression — and that whitelist comes from §11.2.1.
TEST(ConstantFunctionRulesElaboration, NonConstantSystemFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int bad_func(int n);\n"
      "    return $time;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4.3 (h): identifiers must resolve to a parameter, function name, or
// something declared inside the function.
TEST(ConstantFunctionRulesElaboration, ExternalNetReferenceError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] outside;\n"
      "  function int bad_func(int n);\n"
      "    return n + outside;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4.3 (h) positive: a local block-scope variable counts as a local
// declaration.
TEST(ConstantFunctionRulesElaboration, LocalVariableReferenceOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int sum_to(int n);\n"
      "    int acc;\n"
      "    acc = n + 1;\n"
      "    return acc;\n"
      "  endfunction\n"
      "  localparam int P = sum_to(4);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.4.3 (e): no hierarchical references inside the body.
TEST(ConstantFunctionRulesElaboration, HierarchicalReferenceError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int bad_func(int n);\n"
      "    return n + top.sig;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4.3 (k): when a default argument is supplied it must be a constant
// expression in the §11.2.1 sense.
TEST(ConstantFunctionRulesElaboration, NonConstantDefaultArgError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] outside;\n"
      "  function int bad_func(int n = outside);\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int P = bad_func();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4.3 (b): a DPI import is not eligible to back a constant function call.
TEST(ConstantFunctionRulesElaboration, DpiImportCallError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  import \"DPI-C\" function int ext_calc(int n);\n"
      "  localparam int P = ext_calc(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4.3 (c): a delay control schedules execution after the function would
// otherwise return, so it is forbidden in a constant function body.
TEST(ConstantFunctionRulesElaboration, DelayStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int bad_func(int n);\n"
      "    #5;\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4.3 (c): event control inside the body also schedules later execution.
TEST(ConstantFunctionRulesElaboration, EventControlError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  function int bad_func(int n);\n"
      "    @(e);\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4.3 (c): triggering an event is itself an event-scheduling action.
TEST(ConstantFunctionRulesElaboration, EventTriggerError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  function int bad_func(int n);\n"
      "    ->e;\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4.3 definition: arguments to a constant function call must themselves
// be constant expressions; a free net reference is not.
TEST(ConstantFunctionRulesElaboration, NonConstantArgumentError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] runtime_val;\n"
      "  function int passthrough(int n); return n; endfunction\n"
      "  localparam int P = passthrough(runtime_val);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4.3 (c): a wait statement suspends execution past the function's
// natural return, so it cannot appear in a constant function body.
TEST(ConstantFunctionRulesElaboration, WaitStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic done;\n"
      "  function int bad_func(int n);\n"
      "    wait (done);\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4.3 (f): the body must only invoke other constant functions. A task
// call is not a constant function call, so the elaborator must reject it.
TEST(ConstantFunctionRulesElaboration, TaskCallInBodyError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task side_effect; endtask\n"
      "  function int bad_func(int n);\n"
      "    side_effect();\n"
      "    return n;\n"
      "  endfunction\n"
      "  localparam int P = bad_func(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4.3 (f): a constant function that calls another function which is
// not itself a valid constant function must be rejected. The leaf function
// here has an output argument that the outer call hides from the direct
// validation walk — the recursive check needs to catch it.
TEST(ConstantFunctionRulesElaboration, NestedCalleeWithOutputArgError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int leaf(input int a, output int b);\n"
      "    b = 0;\n"
      "    return a;\n"
      "  endfunction\n"
      "  function int parent(int n);\n"
      "    int tmp;\n"
      "    return leaf(n, tmp);\n"
      "  endfunction\n"
      "  localparam int P = parent(4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4.3 (f): two constant functions calling each other must terminate
// (the recursive check guards against cycles) and validate successfully
// when both are well-formed.
TEST(ConstantFunctionRulesElaboration, MutualRecursionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int ping(int n); return pong(n); endfunction\n"
      "  function int pong(int n); return ping(n); endfunction\n"
      "  localparam int P = ping(0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.4.3 definition: a constant function call is EVALUATED at elaboration
// time. A localparam initialized from a user function call must therefore fold
// to the function's return value, not just elaborate without complaint.
TEST(ConstantFunctionElaboration, LocalparamFoldsToFunctionResult) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int calc(int n); return n * 2; endfunction\n"
      "  localparam int P = calc(4);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "P"), 8);
}

// §13.4.3 canonical example: the clogb2 function returns ceil(log2). Its body
// exercises the whole elaboration-time interpreter — a local-variable mutation,
// a for loop, and assignment to the implicit result variable named after the
// function — and must fold clogb2(256) to 8.
TEST(ConstantFunctionElaboration, Clogb2ExampleFoldsAtElaboration) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function integer clogb2(input int value);\n"
      "    value = value - 1;\n"
      "    for (clogb2 = 0; value > 0; clogb2 = clogb2 + 1)\n"
      "      value = value >> 1;\n"
      "  endfunction\n"
      "  localparam addr_width = clogb2(256);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "addr_width"), 8);
}

// §13.4.3: the constant function argument may itself be a parameter reference
// (the LRM example calls clogb2(ram_depth)). The argument is a constant
// expression, so the call still folds.
TEST(ConstantFunctionElaboration, ArgumentFromParameterFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function integer clogb2(input int value);\n"
      "    value = value - 1;\n"
      "    for (clogb2 = 0; value > 0; clogb2 = clogb2 + 1)\n"
      "      value = value >> 1;\n"
      "  endfunction\n"
      "  parameter ram_depth = 256;\n"
      "  localparam addr_width = clogb2(ram_depth);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "addr_width"), 8);
}

// §13.4.3 (f): a constant function body may invoke another constant function.
// The nested calls must fold through: quad(3) = twice(twice(3)) = 12.
TEST(ConstantFunctionElaboration, NestedConstantCallFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int twice(int n); return n * 2; endfunction\n"
      "  function int quad(int n); return twice(twice(n)); endfunction\n"
      "  localparam int P = quad(3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "P"), 12);
}

// §13.4.1 / §13.4.3: the return value can be produced by assigning to the
// implicit variable that shares the function's name; that assignment must be
// honored by the elaboration-time evaluation.
TEST(ConstantFunctionElaboration, FunctionNameResultFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int compute(int n);\n"
      "    compute = n * 3;\n"
      "  endfunction\n"
      "  localparam int P = compute(7);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "P"), 21);
}

// §13.4.3: a constant function may reference a module parameter defined before
// the call. The reference resolves to the parameter's value during the fold:
// adjust(3) with BIAS = 7 is 10.
TEST(ConstantFunctionElaboration, ParameterReferenceInBodyFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int BIAS = 7;\n"
      "  function int adjust(int n); return n + BIAS; endfunction\n"
      "  localparam int P = adjust(3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "P"), 10);
}

// §13.4.3 (g): a constant function may call a system function admissible in a
// constant_expression. $clog2(256) inside the body folds to 8.
TEST(ConstantFunctionElaboration, SystemFunctionInBodyFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int log2_fn(int n); return $clog2(n); endfunction\n"
      "  localparam int W = log2_fn(256);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "W"), 8);
}

// §13.4.3 (k): when a call omits an argument that has a constant default value,
// the fold uses that default. with_default() = 5 * 2 = 10.
TEST(ConstantFunctionElaboration, DefaultArgumentValueFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int with_default(int n = 5); return n * 2; endfunction\n"
      "  localparam int P = with_default();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "P"), 10);
}

// §13.4.3: an if/else selecting the return path folds along the taken branch.
TEST(ConstantFunctionElaboration, ConditionalBodyFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int pick(int n);\n"
      "    if (n > 10) return 100;\n"
      "    else return 1;\n"
      "  endfunction\n"
      "  localparam int P = pick(3);\n"
      "  localparam int Q = pick(50);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "P"), 1);
  EXPECT_EQ(ResolvedParam(design, "Q"), 100);
}

// §13.4.3: a (non-severity) system task call inside a constant function body is
// ignored during elaboration-time evaluation rather than aborting the fold. The
// $display is skipped, yet compute(4) still folds to 8.
TEST(ConstantFunctionElaboration, SystemTaskInBodyIgnoredWhileFolding) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int compute(int n);\n"
      "    $display(\"not emitted during constant evaluation\");\n"
      "    return n * 2;\n"
      "  endfunction\n"
      "  localparam int P = compute(4);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "P"), 8);
}

// §13.4.3: the folded constant function value is usable where a constant
// expression is required — here to size a packed dimension. If clogb2(256) did
// not fold to 8, the width of `x` would be wrong.
TEST(ConstantFunctionElaboration, FoldedValueSizesDeclaration) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int width_of(int depth);\n"
      "    int w;\n"
      "    w = 0;\n"
      "    depth = depth - 1;\n"
      "    while (depth > 0) begin\n"
      "      depth = depth >> 1;\n"
      "      w = w + 1;\n"
      "    end\n"
      "    return w;\n"
      "  endfunction\n"
      "  localparam int P = width_of(256);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "P"), 8);
}

// §13.4.3 / §11.2.1: a constant function call argument may be a localparam
// reference — a constant expression resolved on a different path from a literal
// or a module parameter. calc(SZ) with SZ = 4 folds to 8.
TEST(ConstantFunctionElaboration, ArgumentFromLocalparamFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int SZ = 4;\n"
      "  function int calc(int n); return n * 2; endfunction\n"
      "  localparam int P = calc(SZ);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "P"), 8);
}

// §13.4.3 / §11.2.1: a constant function call is itself a constant expression,
// so it is admissible as the argument of another constant function call. The
// inner call folds first: calc(twice(5)) = calc(10) = 12.
TEST(ConstantFunctionElaboration, ArgumentFromNestedConstantCallFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int twice(int n); return n * 2; endfunction\n"
      "  function int calc(int n); return n + 2; endfunction\n"
      "  localparam int P = calc(twice(5));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "P"), 12);
}

// §13.4.3 (k) / §11.2.1: a default argument value written as a module parameter
// reference is a constant expression and must be accepted; f() then folds to
// D * 2 = 10. (A literal default is covered by DefaultArgumentValueFolds.)
TEST(ConstantFunctionElaboration, DefaultArgumentFromParameterFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int D = 5;\n"
      "  function int f(int n = D); return n * 2; endfunction\n"
      "  localparam int P = f();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "P"), 10);
}

// §13.4.3 (k) / §11.2.1: a localparam reference is likewise a constant
// expression admissible as a default argument value; f() folds to 14.
TEST(ConstantFunctionElaboration, DefaultArgumentFromLocalparamFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int D = 7;\n"
      "  function int f(int n = D); return n * 2; endfunction\n"
      "  localparam int P = f();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "P"), 14);
}

// §13.4.3 (f) exception: calling a built-in method on a variable local to the
// function is explicitly permitted, even though a general non-constant-function
// call would be rejected. Here the array reduction `.sum()` is invoked on a
// body-local array, so no "non-constant invocation" error is raised. (On a
// non-local root the same access would trip the identifier/hierarchical rule,
// as ExternalNetReferenceError / HierarchicalReferenceError show.)
TEST(ConstantFunctionElaboration, BuiltinMethodOnLocalAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f();\n"
      "    int a[3];\n"
      "    a = '{1, 2, 3};\n"
      "    return a.sum();\n"
      "  endfunction\n"
      "  localparam int P = f();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
