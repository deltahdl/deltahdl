#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

// A.3.3 makes a gate's output and inout terminals a net_lvalue, as A.5.4 does
// a user-defined primitive instance's output terminal, and A.8.5 writes the
// selects under the net's name as a constant_select.
const char* const kNonConstant =
    "a primitive's output or inout terminal selects with an expression that "
    "is not constant";

// An index naming a variable is no constant expression, at a gate's output, a
// switch's inout and a UDP instance's output alike (#7978).
TEST(PrimitiveTerminalElaboration, ADrivenTerminalSelectByAVariableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "primitive p(output y, input a);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  wire [3:0] w;\n"
      "  wire a;\n"
      "  logic [1:0] i;\n"
      "  buf b1(w[i], a);\n"
      "  tran t1(w[i], a);\n"
      "  p u1(w[i], a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNonConstant, 8, "A.8.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNonConstant, 9, "A.8.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNonConstant, 10, "A.8.5"));
}

// A parameter, a localparam and the genvar of the loop generate block the
// instance stands in are constant expressions, and a net or a variable named
// whole, which §6.5 lets a primitive drive, selects with nothing.
TEST(PrimitiveTerminalElaboration, ConstantSelectsAndWholeNamesAreNotReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [3:0] w;\n"
      "  wire a, y;\n"
      "  logic v;\n"
      "  localparam int K = 2;\n"
      "  parameter int P = 0;\n"
      "  buf b1(w[K], a);\n"
      "  not n1(w[P + 1], a);\n"
      "  for (genvar k = 0; k < 2; k++) begin : g\n"
      "    buf b2(w[k], a);\n"
      "  end\n"
      "  buf b3(y, a);\n"
      "  not n2(v, a);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNonConstant, 7, "A.8.5"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNonConstant, 8, "A.8.5"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNonConstant, 10, "A.8.5"));
  EXPECT_FALSE(f.has_errors);
}

// A.8.5 names a net in a net_lvalue through ps_or_hierarchical_net_identifier,
// and §6.20 makes a parameter a constant that nothing drives, whether it is
// named whole or selected, and whether the module or a generate block declares
// it (#7981).
TEST(PrimitiveTerminalElaboration, AParameterAsADrivenTerminalIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "primitive p(output y, input a);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  parameter P = 1;\n"
      "  localparam logic [1:0] Q = 0;\n"
      "  wire a;\n"
      "  buf b1(P, a);\n"
      "  tran t1(Q[0], a);\n"
      "  p u1(P, a);\n"
      "  if (1) begin : g\n"
      "    localparam int R = 0;\n"
      "    not n1(R, a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a primitive's output or inout terminal names "
                            "parameter 'P'",
                            8, "A.8.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a primitive's output or inout terminal names "
                            "parameter 'Q'",
                            9, "A.8.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a primitive's output or inout terminal names "
                            "parameter 'P'",
                            10, "A.8.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a primitive's output or inout terminal names "
                            "parameter 'R'",
                            13, "A.8.5"));
}

}  // namespace
