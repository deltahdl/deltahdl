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

}  // namespace
