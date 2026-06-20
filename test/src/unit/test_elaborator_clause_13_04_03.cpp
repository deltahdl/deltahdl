#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ConstantFunctionElaboration, CallInLocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int calc(int n); return n * 2; endfunction\n"
      "  localparam int P = calc(4);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
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

TEST(ConstantFunctionRulesElaboration, SystemFunctionCallOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int log2_fn(int n); return $clog2(n); endfunction\n"
      "  localparam int W = log2_fn(256);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
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

// §13.4.3 (h) positive: a module parameter referenced from the body is fine.
TEST(ConstantFunctionRulesElaboration, ModuleParameterReferenceOk) {
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

// §13.4.3 (k) positive: a literal default value is a constant expression.
TEST(ConstantFunctionRulesElaboration, ConstantDefaultArgOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int with_default(int n = 5);\n"
      "    return n * 2;\n"
      "  endfunction\n"
      "  localparam int P = with_default();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.4.3 (f): the body may invoke another constant function (the recursive
// validation must traverse into it).
TEST(ConstantFunctionRulesElaboration, NestedConstantFunctionCallOk) {
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

// §13.4.3 (h): the constant function name itself is a permitted self-
// reference because the body may assign to a synonym of the function name
// (per §13.4.1) to set the return value.
TEST(ConstantFunctionRulesElaboration, FunctionNameSelfReferenceOk) {
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

}  // namespace
