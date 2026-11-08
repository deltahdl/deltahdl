#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(LoopStatementElaboration, ForLoopTypedInit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForLoopUntypedInit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    for (i = 0; i < 10; i = i + 1) x = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, NestedLoops) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 4; i++) begin\n"
      "      for (int j = 0; j < 4; j++) begin\n"
      "        x = i[7:0] + j[7:0];\n"
      "      end\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForCommaSeparatedTypedInitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    for (int i = 0, int j = 4; i < j; i++, j--)\n"
      "      x = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForTypedInitNotVisibleAfterLoop) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) begin\n"
      "    end\n"
      "    i = 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'i'",
                            5, "23.9"));
}

TEST(LoopStatementElaboration, UntypedForInitVarVisibleAfterLoop) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    for (i = 0; i < 10; i = i + 1) begin\n"
      "    end\n"
      "    i = 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForTypedInitNotReadableAfterLoop) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 3; i++) ;\n"
      "    $display(\"i=%0d\", i);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'i'", 4,
                            "23.9"));
}

TEST(LoopStatementElaboration, ForTypedInitNotReadableAfterLoopInFunction) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  function int f();\n"
      "    for (int i = 0; i < 3; i++) ;\n"
      "    x = i;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'i'", 5,
                            "23.9"));
}

TEST(LoopStatementElaboration, ForTypedInitReadableInsideLoop) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    for (int i = 0, int j = i + 1; i < j; i = i + 1)\n"
      "      x = i + j;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, UntypedForInitVarReadableAfterLoop) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  integer i;\n"
      "  int x;\n"
      "  initial begin\n"
      "    for (i = 0; i < 3; i = i + 1) ;\n"
      "    x = i;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ConstantFunctionForVariableHidesOuterOne) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int f(int n);\n"
      "    int i = 7;\n"
      "    for (int i = 0; i < n; i++) ;\n"
      "    return i;\n"
      "  endfunction\n"
      "  localparam int P = f(3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* p = FindParam(design, "m", "P");
  ASSERT_NE(p, nullptr);
  ASSERT_TRUE(p->is_resolved);
  EXPECT_EQ(p->resolved_value, 7);
}

TEST(LoopStatementElaboration, MethodCallThroughForLoopVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int n;\n"
      "  function automatic int f();\n"
      "    int c = 0;\n"
      "    for (string s = \"\"; s.len() < 3; s = {s, \"x\"}) c += s.len();\n"
      "    return c;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    for (string s = \"\"; s.len() < 3; s = {s, \"x\"}) n++;\n"
      "    n += f();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, MethodCallThroughForLoopVariableAfterTheLoop) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int n;\n"
      "  initial begin\n"
      "    for (string s = \"\"; s.len() < 3; s = {s, \"x\"}) n++;\n"
      "    n = s.len();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name 's' resolves to no declaration",
                            5, "23.8"));
}

}  // namespace
