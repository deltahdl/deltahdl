#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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
  const auto kReported = [&f](std::string_view op, uint32_t line) {
    return ReportedError(f.diag.Diagnostics(),
                         std::string("the property operator '") +
                             std::string(op) +
                             "' joins the operands of an ordinary expression",
                         line, "A.8.6");
  };
  for (uint32_t line : {1u, 3u, 7u, 8u}) {
    EXPECT_TRUE(kReported("|->", line)) << line;
  }
  for (uint32_t line : {4u, 6u, 9u}) {
    EXPECT_TRUE(kReported("|=>", line)) << line;
  }
  const auto& diags = f.diag.Diagnostics();
  EXPECT_EQ(std::count_if(diags.begin(), diags.end(),
                          [](const auto& d) { return d.subclause == "A.8.6"; }),
            7);
}

}  // namespace
