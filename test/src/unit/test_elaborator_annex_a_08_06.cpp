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

::testing::AssertionResult ReportedImplication(const ElabFixture& f,
                                               std::string_view op,
                                               uint32_t line) {
  return ReportedError(f.diag.Diagnostics(),
                       std::string("the property operator '") +
                           std::string(op) +
                           "' joins the operands of an ordinary expression",
                       line, "A.8.6");
}

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

TEST(OperatorElaboration, ImplicationInInstancePortConnectionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module c(input logic i);\n"
      "endmodule\n"
      "checker k(property p);\n"
      "endchecker\n"
      "module m;\n"
      "  logic a, b;\n"
      "  c u1(a & (a |-> b));\n"
      "  c u2(.i(b | (a |=> b)));\n"
      "  c u3(a |-> b);\n"
      "  k u4(a |-> b);\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {7}, {8});
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is an event expression, a sequence or a "
                            "property, which only a checker's port takes",
                            9, "23.3.2"));
}

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

TEST(OperatorElaboration, ImplicationInUdpInstanceTerminalIsError) {
  ElabFixture f;
  ElaborateSrc(
      "primitive u(output o, input i, input j);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire o1;\n"
      "  logic a, b;\n"
      "  u p1(o1, a |-> b, a |=> b);\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {10}, {10});
}

TEST(OperatorElaboration, ImplicationInCovergroupCrossIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  bit [1:0] a, b;\n"
      "  covergroup cg @(posedge clk);\n"
      "    ca: coverpoint a;\n"
      "    cb: coverpoint b;\n"
      "    x: cross ca, cb iff (a[0] |-> b[0]) {\n"
      "      option.weight = 1'b1 |=> 1'b0;\n"
      "      bins s = binsof(ca) intersect {1'b1 |-> 1'b0} iff (a[1] |=> "
      "b[1]);\n"
      "      bins w = binsof(cb) with (cb |-> 1'b1) matches (1'b1 |=> 1'b1);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {7, 9, 10}, {8, 9, 10});
}

TEST(OperatorElaboration, ImplicationInCrossBodyFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  bit [1:0] a, b;\n"
      "  covergroup cg @(posedge clk);\n"
      "    ca: coverpoint a;\n"
      "    cb: coverpoint b;\n"
      "    x: cross ca, cb {\n"
      "      function bit f(bit p = 1'b1 |=> 1'b0);\n"
      "        return a[0] |-> b[0];\n"
      "      endfunction\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {9}, {8});
}

TEST(OperatorElaboration, ImplicationInCovergroupEventOrFormalIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  covergroup cf (int w = 1'b1 |-> 1'b0) @(posedge clk);\n"
      "  endgroup\n"
      "  covergroup cs with function sample (bit v = 1'b1 |=> 1'b0);\n"
      "  endgroup\n"
      "  covergroup ce @(posedge (a |-> b) iff (a |=> b));\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {3, 7}, {5, 7});
}

TEST(OperatorElaboration, ImplicationInTransitionBinIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  bit a;\n"
      "  covergroup cg @(posedge clk);\n"
      "    cp: coverpoint a {\n"
      "      bins t = ((1'b0 |-> 1'b1) => 1'b1 [* (1'b1 |=> 1'b1)]);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {6}, {6});
}

TEST(OperatorElaboration, ImplicationInClassCovergroupIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class c;\n"
      "  bit a, b;\n"
      "  covergroup cg;\n"
      "    option.weight = 1'b1 |-> 1'b0;\n"
      "    cp: coverpoint a |=> b;\n"
      "  endgroup\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  ExpectImplicationReports(f, {4}, {5});
}

}  // namespace
