#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// Whether the A.8.6 report of the property operator `op` stands at `line`.
::testing::AssertionResult ReportedImplication(const ElabFixture& f,
                                               std::string_view op,
                                               uint32_t line) {
  return ReportedError(f.diag.Diagnostics(),
                       std::string("the property operator '") +
                           std::string(op) +
                           "' joins the operands of an ordinary expression",
                       line, "A.8.6");
}

// Expects a `|->` reported at each of `overlapped` and a `|=>` at each of
// `nonoverlapped`, and no other report under A.8.6.
void ExpectImplicationReports(const ElabFixture& f,
                              std::initializer_list<uint32_t> overlapped,
                              std::initializer_list<uint32_t> nonoverlapped) {
  for (uint32_t line : overlapped) {
    EXPECT_TRUE(ReportedImplication(f, "|->", line)) << line;
  }
  for (uint32_t line : nonoverlapped) {
    EXPECT_TRUE(ReportedImplication(f, "|=>", line)) << line;
  }
  const auto& diags = f.diag.Diagnostics();
  EXPECT_EQ(
      std::count_if(diags.begin(), diags.end(),
                    [](const auto& d) { return d.subclause == "A.8.6"; }),
      static_cast<std::ptrdiff_t>(overlapped.size() + nonoverlapped.size()));
}

// A.8.6's binary_operator holds neither `|->` nor `|=>`, which A.2.10 writes
// as property operators alone (§16.12.7), so an ordinary expression joined by
// either is reported wherever it stands: a parameter's value, a continuous
// assignment, a variable's initializer, a procedural assignment, a condition,
// an immediate assertion's expression and a concurrent assertion's action
// block. A concurrent assertion's property, in a module or in a procedure, and
// an expect statement's are property expressions, which hold them legally.
TEST(OperatorElaboration, ImplicationJoiningOrdinaryExpressionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter bit P = 1'b1 |-> 1'b0);\n"
      "  logic clk, a, b, x, w;\n"
      "  assign w = a |-> b;\n"
      "  logic y = a |=> b;\n"
      "  initial begin\n"
      "    x = a |=> b;\n"
      "    if (a |-> b) x = 1;\n"
      "    assert (a |-> b);\n"
      "    assert property (@(posedge clk) a |-> b) else x = a |=> b;\n"
      "    expect (@(posedge clk) a |=> b);\n"
      "  end\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {1, 3, 7, 8}, {4, 6, 9});
}

// A.2.12 writes a let's body and each of its ports' defaults as an
// expression, at module level and among a block's items (A.2.8) alike, and an
// expression holds no property operator.
TEST(OperatorElaboration, ImplicationInLetDeclarationIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  let e = a |-> b;\n"
      "  let g(x = a |=> b) = x;\n"
      "  initial begin\n"
      "    let h = a |=> b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {3}, {4, 6});
}

// A.2.7 writes a task's or a function's port default as an expression.
TEST(OperatorElaboration, ImplicationInSubroutinePortDefaultIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function bit f(bit a, bit b = 1'b1 |-> 1'b0);\n"
      "    return a;\n"
      "  endfunction\n"
      "  task t(input bit c = 1'b1 |=> 1'b0);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {2}, {5});
}

// A class's parameter values, a property's initializer, a constraint
// (A.1.10), a method's statements, a nested class's own and the arguments a
// class hands its base's constructor are all expressions. The implication a
// constraint does hold is `->`.
TEST(OperatorElaboration, ImplicationInClassDeclarationIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class c #(parameter bit P = 1'b1 |-> 1'b0);\n"
      "    rand bit a, b;\n"
      "    bit y = 1'b1 |=> 1'b0;\n"
      "    constraint k { a |-> b; soft b |=> a; }\n"
      "    function new(bit v);\n"
      "      a = v |-> b;\n"
      "    endfunction\n"
      "    class n;\n"
      "      bit z = 1'b0 |=> 1'b1;\n"
      "    endclass\n"
      "  endclass\n"
      "  class d extends c(1'b1 |-> 1'b0);\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {2, 5, 7, 13}, {4, 5, 10});
}

// A package's declarations and those of the compilation unit outside every
// design element (§3.12.1) hold ordinary expressions as a module's do.
TEST(OperatorElaboration, ImplicationInPackageAndUnitScopeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  parameter bit P = 1'b1 |-> 1'b0;\n"
      "  bit v = 1'b1 |=> 1'b0;\n"
      "  function bit f(bit a, bit b);\n"
      "    return a |-> b;\n"
      "  endfunction\n"
      "endpackage\n"
      "bit w = 1'b1 |=> 1'b0;\n"
      "function bit g(bit a, bit b);\n"
      "  return a |-> b;\n"
      "endfunction\n"
      "class k;\n"
      "  bit u = 1'b0 |=> 1'b1;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {2, 5, 10}, {3, 8, 13});
}

// A.4.1.1 writes a module instance's ordered and named port connections as
// expressions. A checker instance's are property_actual_args (A.4.1.4), which
// may hold a property.
TEST(OperatorElaboration, ImplicationInInstancePortConnectionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module c(input logic i);\n"
      "endmodule\n"
      "checker k(property p);\n"
      "endchecker\n"
      "module m;\n"
      "  logic a, b;\n"
      "  c u1(a |-> b);\n"
      "  c u2(.i(a |=> b));\n"
      "  k u3(a |-> b);\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {7}, {8});
}

// A.4.1.1 writes an ordered and a named parameter value as a param_expression.
TEST(OperatorElaboration, ImplicationInInstanceParameterValueIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module c #(parameter bit P = 0, parameter bit Q = 0);\n"
      "endmodule\n"
      "module m;\n"
      "  c #(1'b1 |-> 1'b0) u1();\n"
      "  c #(.Q(1'b0 |=> 1'b1)) u2();\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {4}, {5});
}

// A.3.3 writes a gate's input and enable terminals as expressions.
TEST(OperatorElaboration, ImplicationInGateTerminalIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire o1, o2;\n"
      "  logic a, b, e;\n"
      "  and g1(o1, a |-> b, e);\n"
      "  bufif1 g2(o2, a, e |=> b);\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {4}, {5});
}

// A.4.2 writes an if-generate construct's condition as a constant expression,
// that of an else-if among them.
TEST(OperatorElaboration, ImplicationInIfGenerateConditionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  localparam bit A = 1, B = 0;\n"
      "  if (A |-> B) begin : g1\n"
      "  end else if (B |=> A) begin : g2\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {3}, {4});
}

// A.4.2 writes a case-generate construct's selector and item values as
// constant expressions.
TEST(OperatorElaboration, ImplicationInCaseGenerateIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  localparam bit A = 1, B = 0;\n"
      "  case (A |-> B)\n"
      "    B |=> A: begin : g1 end\n"
      "    default: begin : g2 end\n"
      "  endcase\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {3}, {4});
}

// A.4.2 writes a loop-generate construct's initialization, condition and
// iteration as expressions.
TEST(OperatorElaboration, ImplicationInLoopGenerateHeaderIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  localparam bit A = 1, B = 0;\n"
      "  genvar i;\n"
      "  for (i = A |-> B; i < 1; i = i + 1) begin : g1\n"
      "  end\n"
      "  for (i = 0; i < (A |=> B) + 1; i = i + 1) begin : g2\n"
      "  end\n"
      "  for (i = 0; i < 1; i = i + (B |-> A) + 1) begin : g3\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {4, 8}, {6});
}

// A.2.11 writes a covergroup option's value, a coverpoint's expression and
// guard, and a bin's option, values, array size, filter, set expression and
// guard as expressions.
TEST(OperatorElaboration, ImplicationInCovergroupIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  covergroup cg @(posedge clk);\n"
      "    option.weight = 1'b1 |-> 1'b0;\n"
      "    cp: coverpoint a |=> b iff (a |-> b) {\n"
      "      option.weight = 1'b0 |=> 1'b1;\n"
      "      bins one = {1'b1 |-> 1'b0, [1'b0 : 1'b1 |=> 1'b0]};\n"
      "      bins arr[1'b1 |-> 1'b1] = {0} iff (b |=> a);\n"
      "      bins w = {[0:1]} with (item |-> 1'b1);\n"
      "      bins s = a |=> b;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {4, 5, 7, 8, 9}, {5, 6, 7, 8, 10});
}

}  // namespace
