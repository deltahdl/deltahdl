#include <gtest/gtest.h>

#include <cstdint>
#include <string>

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

uint64_t ValueAfterRun(SimFixture& f, const char* name) {
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr) << name;
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

SimFixture* RunCountdrivers(SimFixture& f, const std::string& src) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (design != nullptr) LowerAndRun(design, f);
  return &f;
}

TEST(OptionalCountDriversSim, ForcedThenReleasedNetIsNoLongerForced) {
  SimFixture f;
  RunCountdrivers(f,
                  "module t;\n"
                  "  wire w;\n"
                  "  logic a;\n"
                  "  integer during, after;\n"
                  "  assign w = a;\n"
                  "  initial begin\n"
                  "    a = 0;\n"
                  "    #1 force w = 1'b1;\n"
                  "    #1 $countdrivers(w, during);\n"
                  "    release w;\n"
                  "    #1 $countdrivers(w, after);\n"
                  "  end\n"
                  "endmodule\n");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ValueAfterRun(f, "during"), 1u);
  EXPECT_EQ(ValueAfterRun(f, "after"), 0u);
}

TEST(OptionalCountDriversSim, ForceIsNotCountedAmongTheDrivers) {
  SimFixture f;
  RunCountdrivers(f,
                  "module t;\n"
                  "  wire w;\n"
                  "  logic a, b;\n"
                  "  integer fc, c01x, c0, c1, cx;\n"
                  "  assign w = a;\n"
                  "  assign w = b;\n"
                  "  initial begin\n"
                  "    a = 1; b = 1'bx;\n"
                  "    #1 force w = 1'b0;\n"
                  "    #1 $countdrivers(w, fc, c01x, c0, c1, cx);\n"
                  "  end\n"
                  "endmodule\n");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ValueAfterRun(f, "fc"), 1u);
  EXPECT_EQ(ValueAfterRun(f, "c01x"), 2u);
  EXPECT_EQ(ValueAfterRun(f, "c0"), 0u);
  EXPECT_EQ(ValueAfterRun(f, "c1"), 1u);
  EXPECT_EQ(ValueAfterRun(f, "cx"), 1u);
}

TEST(OptionalCountDriversSim, GateAndPortDriversAreCountedLikeAssignments) {
  SimFixture f;
  RunCountdrivers(f,
                  "module src(output wire o);\n"
                  "  assign o = 1'b1;\n"
                  "endmodule\n"
                  "module t;\n"
                  "  wire g1, g2, p1, p2;\n"
                  "  logic a, b;\n"
                  "  integer ng1, ng2, np1, np2;\n"
                  "  buf (g1, a);\n"
                  "  buf (g2, a);\n"
                  "  buf (g2, b);\n"
                  "  src u1(p1);\n"
                  "  src u2(p2);\n"
                  "  src u3(p2);\n"
                  "  initial begin\n"
                  "    a = 1; b = 0;\n"
                  "    #1;\n"
                  "    ng1 = $countdrivers(g1);\n"
                  "    ng2 = $countdrivers(g2);\n"
                  "    np1 = $countdrivers(p1);\n"
                  "    np2 = $countdrivers(p2);\n"
                  "  end\n"
                  "endmodule\n");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ValueAfterRun(f, "ng1"), 0u);
  EXPECT_EQ(ValueAfterRun(f, "ng2"), 1u);
  EXPECT_EQ(ValueAfterRun(f, "np1"), 0u);
  EXPECT_EQ(ValueAfterRun(f, "np2"), 1u);
}

TEST(OptionalCountDriversSim, ReturnValueInsideAnExpressionBesideOutputs) {
  SimFixture f;
  RunCountdrivers(f,
                  "module t;\n"
                  "  wire w;\n"
                  "  logic a, b;\n"
                  "  integer n, fc, c01x;\n"
                  "  assign w = a;\n"
                  "  assign w = b;\n"
                  "  initial begin\n"
                  "    a = 1; b = 0;\n"
                  "    #1 n = $countdrivers(w, fc, c01x) + 4;\n"
                  "  end\n"
                  "endmodule\n");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ValueAfterRun(f, "n"), 5u);
  EXPECT_EQ(ValueAfterRun(f, "fc"), 0u);
  EXPECT_EQ(ValueAfterRun(f, "c01x"), 2u);
}

TEST(OptionalCountDriversSim, CallInEveryProceduralPlaceReturnsTheSame) {
  const char* const kPlaces[] = {
      "module t;\n  wire w;\n  logic a, b;\n  integer n;\n"
      "  assign w = a;\n  assign w = b;\n"
      "  function automatic integer f();\n    return $countdrivers(w);\n"
      "  endfunction\n  initial begin\n    a = 1; b = 0;\n    #1 n = f();\n"
      "  end\nendmodule\n",
      "module t;\n  wire w;\n  logic a, b;\n  integer n;\n"
      "  assign w = a;\n  assign w = b;\n"
      "  task automatic tk();\n    n = $countdrivers(w);\n  endtask\n"
      "  initial begin\n    a = 1; b = 0;\n    #1 tk();\n  end\nendmodule\n",
      "module t;\n  wire w;\n  logic a, b;\n  integer n;\n"
      "  assign w = a;\n  assign w = b;\n"
      "  initial begin\n    a = 1; b = 0;\n  end\n"
      "  always @(w) n = $countdrivers(w);\nendmodule\n",
      "module t;\n  wire w;\n  logic a, b;\n  integer n;\n"
      "  assign w = a;\n  assign w = b;\n"
      "  initial begin\n    a = 1; b = 0;\n  end\n"
      "  final n = $countdrivers(w);\nendmodule\n",
      "program t;\n  wire w;\n  logic a, b;\n  integer n;\n"
      "  assign w = a;\n  assign w = b;\n"
      "  initial begin\n    a = 1; b = 0;\n    #1 n = $countdrivers(w);\n"
      "  end\nendprogram\n",
      "interface ifc;\n  wire w;\n  logic a, b;\n  integer n;\n"
      "  assign w = a;\n  assign w = b;\n"
      "  initial begin\n    a = 1; b = 0;\n    #1 n = $countdrivers(w);\n"
      "  end\nendinterface\n"
      "module t;\n  ifc ii();\n  integer n;\n  initial #2 n = "
      "ii.n;\nendmodule\n",
  };
  for (const char* src : kPlaces) {
    EXPECT_EQ(RunAndGet(src, "n"), 1u) << src;
  }
}

TEST(OptionalCountDriversSim, EachShorterOutputListWritesOnlyWhatItNames) {
  SimFixture f;
  RunCountdrivers(f,
                  "module t;\n"
                  "  wire w;\n"
                  "  logic a, b;\n"
                  "  integer f3, z3, c3, f4, z4, c4, o4, f5, z5, c5, o5, x5;\n"
                  "  assign w = a;\n"
                  "  assign w = b;\n"
                  "  initial begin\n"
                  "    {f3, z3, c3, f4, z4, c4, o4, f5, z5, c5, o5, x5} = '1;\n"
                  "    a = 1; b = 0;\n"
                  "    #1;\n"
                  "    $countdrivers(w, f3, z3);\n"
                  "    $countdrivers(w, f4, z4, c4);\n"
                  "    $countdrivers(w, f5, z5, c5, o5);\n"
                  "  end\n"
                  "endmodule\n");
  EXPECT_FALSE(f.has_errors);
  const uint64_t kUntouched = 0xFFFFFFFFu;
  EXPECT_EQ(ValueAfterRun(f, "f3"), 0u);
  EXPECT_EQ(ValueAfterRun(f, "z3"), 2u);
  EXPECT_EQ(ValueAfterRun(f, "c3"), kUntouched);
  EXPECT_EQ(ValueAfterRun(f, "f4"), 0u);
  EXPECT_EQ(ValueAfterRun(f, "z4"), 2u);
  EXPECT_EQ(ValueAfterRun(f, "c4"), 1u);
  EXPECT_EQ(ValueAfterRun(f, "o4"), kUntouched);
  EXPECT_EQ(ValueAfterRun(f, "f5"), 0u);
  EXPECT_EQ(ValueAfterRun(f, "z5"), 2u);
  EXPECT_EQ(ValueAfterRun(f, "c5"), 1u);
  EXPECT_EQ(ValueAfterRun(f, "o5"), 1u);
  EXPECT_EQ(ValueAfterRun(f, "x5"), kUntouched);
}

TEST(OptionalCountDriversSim, OutputsOfOtherIntegralTypesTakeTheValue) {
  SimFixture f;
  RunCountdrivers(f,
                  "module t;\n"
                  "  wire w;\n"
                  "  logic a, b;\n"
                  "  int fc;\n"
                  "  bit [31:0] c01x;\n"
                  "  logic [3:0] c0;\n"
                  "  bit [1:0] c1;\n"
                  "  bit narrow;\n"
                  "  assign w = a;\n"
                  "  assign w = b;\n"
                  "  initial begin\n"
                  "    a = 1; b = 0;\n"
                  "    #1 $countdrivers(w, fc, c01x, c0, c1);\n"
                  "    $countdrivers(w, fc, narrow);\n"
                  "  end\n"
                  "endmodule\n");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ValueAfterRun(f, "fc"), 0u);
  EXPECT_EQ(ValueAfterRun(f, "c01x"), 2u);
  EXPECT_EQ(ValueAfterRun(f, "c0"), 1u);
  EXPECT_EQ(ValueAfterRun(f, "c1"), 1u);
  EXPECT_EQ(ValueAfterRun(f, "narrow"), 0u);
}

TEST(OptionalCountDriversSim, NonConstantBitSelectCountsTheBitItSelects) {
  EXPECT_EQ(
      RunAndGet("module t;\n"
                "  wire [3:0] v;\n"
                "  logic [3:0] seen;\n"
                "  integer k;\n"
                "  assign v = 4'b0101;\n"
                "  assign v[2] = 1'b1;\n"
                "  initial begin\n"
                "    #1;\n"
                "    for (k = 0; k < 4; k++) seen[k] = $countdrivers(v[k]);\n"
                "  end\n"
                "endmodule\n",
                "seen"),
      0b0100u);
}

TEST(OptionalCountDriversSim, EveryNetTypeIsCounted) {
  const char* const kNetTypes[] = {"wire",    "tri",     "wand",
                                   "wor",     "tri0",    "tri1",
                                   "supply0", "supply1", "trireg"};
  for (const char* type : kNetTypes) {
    std::string src = "module t;\n  ";
    src += type;
    src += " one, two;\n  ";
    src += type;
    src +=
        " [1:0] vv;\n"
        "  logic a, b;\n"
        "  logic [3:0] seen;\n"
        "  assign one = a;\n"
        "  assign two = a;\n"
        "  assign two = b;\n"
        "  assign vv[0] = a;\n"
        "  assign vv[1] = a;\n"
        "  assign vv[1] = b;\n"
        "  initial begin\n"
        "    a = 1; b = 0;\n"
        "    #1 seen = {$countdrivers(one), $countdrivers(two),\n"
        "               $countdrivers(vv[0]), $countdrivers(vv[1])};\n"
        "  end\n"
        "endmodule\n";
    EXPECT_EQ(RunAndGet(src, "seen"), 0b0101u) << type;
  }
  EXPECT_EQ(
      RunAndGet("module t;\n"
                "  uwire one;\n"
                "  uwire [1:0] vv;\n"
                "  logic a;\n"
                "  logic [1:0] seen;\n"
                "  assign one = a;\n"
                "  assign vv = {a, a};\n"
                "  initial begin\n"
                "    a = 1;\n"
                "    #1 seen = {$countdrivers(one), $countdrivers(vv[1])};\n"
                "  end\n"
                "endmodule\n",
                "seen"),
      0u);
}

TEST(OptionalCountDriversSim, DISABLED_HierarchicalNetReferencesAreCounted) {
  EXPECT_EQ(
      RunAndGet("module src(output wire o, output wire [1:0] ov);\n"
                "  assign o = 1'b1;\n"
                "  assign ov = 2'b10;\n"
                "endmodule\n"
                "interface ifc;\n"
                "  wire w;\n"
                "endinterface\n"
                "module t;\n"
                "  wire p;\n"
                "  wire [1:0] pv;\n"
                "  logic a;\n"
                "  logic [2:0] seen;\n"
                "  src u(p, pv);\n"
                "  assign p = a;\n"
                "  assign pv[1] = a;\n"
                "  ifc ii();\n"
                "  assign ii.w = a;\n"
                "  initial begin\n"
                "    a = 1;\n"
                "    #1 seen = {$countdrivers(u.o), $countdrivers(u.ov[1]),\n"
                "               $countdrivers(ii.w)};\n"
                "  end\n"
                "endmodule\n",
                "seen"),
      0b110u);
}

constexpr const char* kNoNetReport =
    "$countdrivers takes a scalar net or a bit-select of a vector net, and its "
    "net argument names no net";

TEST(OptionalCountDriversSim, AnExpressionThatIsNoNetReferenceIsRejected) {
  const char* const kArguments[] = {"w & w2", "~w", "{w, w2}", "1'b0", ""};
  for (const char* argument : kArguments) {
    std::string src =
        "module t;\n  wire w, w2;\n  integer n;\n  initial n = $countdrivers(";
    src += argument;
    src += ");\nendmodule\n";
    SimFixture f;
    RunCountdrivers(f, src);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoNetReport, 4, "D.2"))
        << src;
  }
}

TEST(OptionalCountDriversSim, DISABLED_APartSelectOfAVectorNetIsRejected) {
  const char* const kArguments[] = {"v[1:0]", "v[0+:2]", "v[3-:2]"};
  for (const char* argument : kArguments) {
    std::string src =
        "module t;\n  wire [3:0] v;\n  integer n;\n  initial n = "
        "$countdrivers(";
    src += argument;
    src += ");\nendmodule\n";
    SimFixture f;
    RunCountdrivers(f, src);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "$countdrivers takes a scalar net or a "
                              "bit-select of a vector net",
                              4, "D.2"))
        << src;
  }
}

TEST(OptionalCountDriversSim, SixArgumentsAreAccepted) {
  SimFixture f;
  RunCountdrivers(f,
                  "module t;\n"
                  "  wire w;\n"
                  "  integer n;\n"
                  "  initial $countdrivers(w, n, n, n, n, n);\n"
                  "endmodule\n");
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), 4));
}

TEST(OptionalCountDriversSim, DISABLED_SevenArgumentsAreRejected) {
  SimFixture f;
  RunCountdrivers(f,
                  "module t;\n"
                  "  wire w;\n"
                  "  integer n;\n"
                  "  initial $countdrivers(w, n, n, n, n, n, n);\n"
                  "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "$countdrivers", 4, "D.2"));
}

}  // namespace
