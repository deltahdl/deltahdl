#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// Annex D.2: $countdrivers returns 1 to flag bus contention when a net is
// driven by more than one driver. Two continuous assignments place two drivers
// on w.
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

// Annex D.2: $countdrivers returns 0 when the net has no more than one driver,
// so a single continuous assignment is not contention.
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

// Annex D.2 / Table D.1: the optional output arguments receive, in declared
// order, net_is_forced, number_of_01x_drivers, and the per-state 0/1/x tallies.
// Here one driver holds 1 and the other holds 0.
TEST(OptionalCountDriversSim, OptionalArgsCarryTableD1Tallies) {
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

// Annex D.2 / Table D.1: a driver in the high-impedance (z) state is not
// actively driving and is excluded from the 0/1/x tallies, while an x driver is
// counted as an x driver.
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

// Annex D.2: the specified net may be a bit-select of a vector net, and the
// count is taken on that selected bit. Two whole-vector drivers drive bit 0 the
// same (contention) but only one of them actively drives bit 1 (the other is
// z), so the same pair of drivers yields a different verdict per selected bit.
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

// Annex D.2: "no more than one driver" includes the zero-driver case, so an
// undriven net reports no contention (0) and every Table D.1 tally is zero.
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

// Annex D.2 / Table D.1: drivers sharing a state are each tallied in that
// state's count, and two drivers -- even with identical values -- still flag
// contention. Here both drivers hold 0, so number_of_0_drivers is 2.
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

// Annex D.2 / Table D.1: the net_is_forced output argument reports 1 once the
// net has been forced.
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

// Annex D.2: "The specified net shall be a scalar or a bit-select of a vector
// net." A vector net named whole is neither, and the call is reported rather
// than answered from the vector's bit 0 -- which, driven twice here, would
// have flagged contention as if the argument were the bit-select it is not.
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

// The same rule for an argument that is no net at all, a variable here: the
// drivers of no net were counted and the call answered 0 in silence.
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
