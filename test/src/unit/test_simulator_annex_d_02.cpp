#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(OptionalCountDriversSim, MultipleDriversReportContention) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wire w;\n"
                      "  logic a, b;\n"
                      "  integer n;\n"
                      "  assign w = a;\n"
                      "  assign w = b;\n"
                      "  initial begin\n"
                      "    a = 1; b = 0;\n"
                      "    #1;\n"
                      "    n = $countdrivers(w);\n"
                      "  end\n"
                      "endmodule\n",
                      "n"),
            1u);
}

TEST(OptionalCountDriversSim, SingleDriverIsNotContention) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wire w;\n"
                      "  logic a;\n"
                      "  integer n;\n"
                      "  assign w = a;\n"
                      "  initial begin\n"
                      "    a = 1;\n"
                      "    #1;\n"
                      "    n = $countdrivers(w);\n"
                      "  end\n"
                      "endmodule\n",
                      "n"),
            0u);
}

TEST(OptionalCountDriversSim, OptionalArgsCarryForcedStateAndDriverTallies) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  logic a, b;\n"
      "  integer fc, c01x, c0, c1, cx;\n"
      "  assign w = a;\n"
      "  assign w = b;\n"
      "  initial begin\n"
      "    a = 1; b = 0;\n"
      "    #1;\n"
      "    $countdrivers(w, fc, c01x, c0, c1, cx);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design,
      {{"fc", 0u}, {"c01x", 2u}, {"c0", 1u}, {"c1", 1u}, {"cx", 0u}});
}

TEST(OptionalCountDriversSim, HighImpedanceExcludedAndXCounted) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  integer fc, c01x, c0, c1, cx;\n"
      "  assign w = 1'bz;\n"
      "  assign w = 1'bx;\n"
      "  initial begin\n"
      "    #1;\n"
      "    $countdrivers(w, fc, c01x, c0, c1, cx);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"c01x", 1u}, {"c0", 0u}, {"c1", 0u}, {"cx", 1u}});
}

TEST(OptionalCountDriversSim, BitSelectOfVectorNetCountsSelectedBit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [3:0] v;\n"
      "  integer nb0, nb1;\n"
      "  assign v = 4'b0011;\n"
      "  assign v = 4'b00z1;\n"
      "  initial begin\n"
      "    #1;\n"
      "    nb0 = $countdrivers(v[0]);\n"
      "    nb1 = $countdrivers(v[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"nb0", 1u}, {"nb1", 0u}});
}

TEST(OptionalCountDriversSim, NoDriversReportNoContention) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  integer n, fc, c01x, c0, c1, cx;\n"
      "  initial begin\n"
      "    #1;\n"
      "    n = $countdrivers(w);\n"
      "    $countdrivers(w, fc, c01x, c0, c1, cx);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"n", 0u},
                    {"fc", 0u},
                    {"c01x", 0u},
                    {"c0", 0u},
                    {"c1", 0u},
                    {"cx", 0u}});
}

TEST(OptionalCountDriversSim, DriversInSameStateBothTallied) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  logic a, b;\n"
      "  integer n, fc, c01x, c0, c1, cx;\n"
      "  assign w = a;\n"
      "  assign w = b;\n"
      "  initial begin\n"
      "    a = 0; b = 0;\n"
      "    #1;\n"
      "    n = $countdrivers(w);\n"
      "    $countdrivers(w, fc, c01x, c0, c1, cx);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design, {{"n", 1u}, {"c01x", 2u}, {"c0", 2u}, {"c1", 0u}, {"cx", 0u}});
}

TEST(OptionalCountDriversSim, NetIsForcedReportedAfterForce) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  wire w;\n"
                      "  logic a;\n"
                      "  integer fc;\n"
                      "  assign w = a;\n"
                      "  initial begin\n"
                      "    a = 1;\n"
                      "    force w = 0;\n"
                      "    #1;\n"
                      "    $countdrivers(w, fc);\n"
                      "  end\n"
                      "endmodule\n",
                      "fc"),
            1u);
}

TEST(OptionalCountDriversSim, AVectorNetNamedWholeIsRejected) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [3:0] v;\n"
      "  integer n;\n"
      "  assign v = 4'b0001;\n"
      "  assign v = 4'b0001;\n"
      "  initial begin\n"
      "    #1;\n"
      "    n = $countdrivers(v);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$countdrivers takes a scalar net or a bit-select "
                            "of a vector net, and its net argument names a "
                            "vector net whole and no bit-select of it",
                            8, "D.2"));
  auto* n = f.ctx.FindVariable("n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 0u);
}

TEST(OptionalCountDriversSim, AnArgumentNamingNoNetIsRejected) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic r;\n"
      "  integer n;\n"
      "  initial n = $countdrivers(r);\n"
      "endmodule\n",
      f);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$countdrivers takes a scalar net or a bit-select "
                            "of a vector net, and its net argument names no "
                            "net",
                            4, "D.2"));
}

}  // namespace
