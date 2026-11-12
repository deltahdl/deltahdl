#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <iterator>

#include "elaborator/elaborator.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(FunctionLifetimeElaboration, DefaultLifetimeFunctionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int adder(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionLifetimeElaboration, RecursiveAutomaticFunctionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int factorial(int n);\n"
      "    if (n <= 1) return 1;\n"
      "    return n * factorial(n - 1);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionLifetimeElaboration, AutoFunctionItemHierRefInContAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  function automatic int g();\n"
      "    int x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  assign y = g.x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic function", 7, "13.4.2"));
}

TEST(FunctionLifetimeElaboration, StaticFunctionItemHierRefAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  function static int g();\n"
      "    int x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  assign y = g.x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionLifetimeElaboration, AutoFunctionItemHierRefInInitialError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  function automatic int g();\n"
      "    int x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  initial y = g.x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic function", 7, "13.4.2"));
}

TEST(FunctionLifetimeElaboration,
     AutoFunctionItemHierRefInAnAssertionPassStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  logic ok;\n"
      "  function automatic int g();\n"
      "    int x;\n"
      "    return x;\n"
      "  endfunction\n"
      "  initial assert (ok) y = g.x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic function", 8, "13.4.2"));
}

TEST(FunctionLifetimeElaboration,
     AutoFunctionItemHierRefInAnAssertionFailStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic held;\n"
      "  logic armed;\n"
      "  function automatic int drain();\n"
      "    int depth;\n"
      "    return depth;\n"
      "  endfunction\n"
      "  initial assert (armed) else held = drain.depth;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic function", 8, "13.4.2"));
}

TEST(FunctionLifetimeElaboration, AutoFunctionItemHierRefInARandcaseItemError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic taken;\n"
      "  function automatic int pick();\n"
      "    int chosen;\n"
      "    return chosen;\n"
      "  endfunction\n"
      "  initial randcase 1: taken = pick.chosen; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic function", 7, "13.4.2"));
}

TEST(FunctionLifetimeElaboration,
     AutoFunctionItemHierRefInARandsequenceCodeBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic kept;\n"
      "  function automatic int sample();\n"
      "    int sampled;\n"
      "    return sampled;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { kept = sample.sampled; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical reference to object in automatic function", 9, "13.4.2"));
}

struct PathIntoAnAutomaticFunction {
  const char* src;
  uint32_t line;
};

void ExpectEachPathReported(const PathIntoAnAutomaticFunction* paths,
                            size_t count) {
  for (size_t i = 0; i < count; ++i) {
    SCOPED_TRACE(paths[i].src);
    ElabFixture f;
    ElaborateSrc(paths[i].src, f);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(),
                      "hierarchical reference to object in automatic function",
                      paths[i].line, "13.4.2"));
  }
}

TEST(FunctionLifetimeElaboration,
     AnItemOfAnImplicitlyAutomaticFunctionOrAnArgumentIsReportedByPath) {
  const PathIntoAnAutomaticFunction kPaths[] = {
      {"module automatic m;\n  function int g();\n    int x;\n"
       "    return x;\n  endfunction\n  int y;\n  initial y = g.x;\n"
       "endmodule\n",
       7},
      {"program automatic p;\n  function int g();\n    int x;\n"
       "    return x;\n  endfunction\n  int y;\n  initial y = g.x;\n"
       "endprogram\n",
       7},
      {"module m;\n  function automatic int g(int a);\n    return a;\n"
       "  endfunction\n  int y;\n  initial y = g.a;\nendmodule\n",
       6},
  };
  ExpectEachPathReported(kPaths, std::size(kPaths));
}

TEST(FunctionLifetimeElaboration,
     DISABLED_AnAutomaticFunctionsItemIsReportedThroughAnInstanceOrBlock) {
  const PathIntoAnAutomaticFunction kPaths[] = {
      {"module c;\n  function automatic int g();\n    int x;\n"
       "    return x;\n  endfunction\nendmodule\nmodule m;\n  c u();\n"
       "  int y;\n  initial y = u.g.x;\nendmodule\n",
       10},
      {"interface i;\n  function automatic int g();\n    int x;\n"
       "    return x;\n  endfunction\nendinterface\nmodule m;\n  i u();\n"
       "  int y;\n  initial y = u.g.x;\nendmodule\n",
       10},
      {"interface automatic i;\n  function int g();\n    int x;\n"
       "    return x;\n  endfunction\nendinterface\nmodule m;\n  i u();\n"
       "  int y;\n  initial y = u.g.x;\nendmodule\n",
       10},
      {"module m;\n  if (1) begin : gb\n    function automatic int g();\n"
       "      int x;\n      return x;\n    endfunction\n  end\n  int y;\n"
       "  initial y = gb.g.x;\nendmodule\n",
       9},
  };
  ExpectEachPathReported(kPaths, std::size(kPaths));
}

}  // namespace
