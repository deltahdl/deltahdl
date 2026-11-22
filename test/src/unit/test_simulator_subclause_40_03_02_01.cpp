#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "simulator/coverage_control.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

constexpr int kStart = 0;
constexpr int kStop = 1;
constexpr int kReset = 2;
constexpr int kCheck = 3;

constexpr int kToggle = 23;

constexpr int kOk = static_cast<int>(CoverageStatus::kOk);
constexpr int kError = static_cast<int>(CoverageStatus::kError);
constexpr int kNoCov = static_cast<int>(CoverageStatus::kNoCoverage);
constexpr int kPartial = static_cast<int>(CoverageStatus::kPartial);

constexpr std::string_view kScope = "$root.tb.unit1";

int RunControl(SimFixture& f, int control, std::string_view scope) {
  auto* call = MkSysCall(
      f.arena, "$coverage_control",
      {MkInt(f.arena, static_cast<uint64_t>(control)), MkInt(f.arena, kToggle),
       MkInt(f.arena, 11), MkStr(f.arena, scope)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

CoverageControlState& Cov(SimFixture& f) {
  return f.ctx.GetCoverageControlState();
}

TEST(CoverageControl, StartOnFullScopeCollectsAndReportsOk) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kFull);

  EXPECT_EQ(RunControl(f, kStart, kScope), kOk);
  EXPECT_TRUE(Cov(f).IsCollecting(std::string(kScope), kToggle));
}

TEST(CoverageControl, StartOnPartialScopeReportsPartial) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kPartial);

  EXPECT_EQ(RunControl(f, kStart, kScope), kPartial);
  EXPECT_TRUE(Cov(f).IsCollecting(std::string(kScope), kToggle));
}

TEST(CoverageControl, StartOnUncoverableScopeReportsNoCoverage) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kNone);

  EXPECT_EQ(RunControl(f, kStart, kScope), kNoCov);
  EXPECT_FALSE(Cov(f).IsCollecting(std::string(kScope), kToggle));
}

TEST(CoverageControl, CheckReportsAvailabilityWithoutCollecting) {
  SimFixture f;
  Cov(f).SetAvailability("full", kToggle, CoverageAvailability::kFull);
  Cov(f).SetAvailability("part", kToggle, CoverageAvailability::kPartial);
  Cov(f).SetAvailability("none", kToggle, CoverageAvailability::kNone);

  EXPECT_EQ(RunControl(f, kCheck, "full"), kOk);
  EXPECT_EQ(RunControl(f, kCheck, "part"), kPartial);
  EXPECT_EQ(RunControl(f, kCheck, "none"), kNoCov);
  EXPECT_FALSE(Cov(f).IsCollecting("full", kToggle));
}

TEST(CoverageControl, StopHaltsCollectionAndReportsOk) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kFull);
  RunControl(f, kStart, kScope);

  EXPECT_EQ(RunControl(f, kStop, kScope), kOk);
  EXPECT_FALSE(Cov(f).IsCollecting(std::string(kScope), kToggle));
}

TEST(CoverageControl, ResetClearsCoverageAndReportsOk) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kFull);
  RunControl(f, kStart, kScope);

  EXPECT_EQ(RunControl(f, kReset, kScope), kOk);
  EXPECT_EQ(Cov(f).ResetCount(std::string(kScope), kToggle), 1U);
}

TEST(CoverageControl, RepeatedStartHasNoEffect) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kFull);

  EXPECT_EQ(RunControl(f, kStart, kScope), kOk);
  EXPECT_EQ(RunControl(f, kStart, kScope), kOk);
  EXPECT_TRUE(Cov(f).IsCollecting(std::string(kScope), kToggle));
  EXPECT_EQ(Cov(f).StartCount(std::string(kScope), kToggle), 1U);
}

TEST(CoverageControl, RepeatedStopHasNoEffect) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kFull);
  RunControl(f, kStart, kScope);

  EXPECT_EQ(RunControl(f, kStop, kScope), kOk);
  EXPECT_EQ(RunControl(f, kStop, kScope), kOk);
  EXPECT_EQ(Cov(f).StopCount(std::string(kScope), kToggle), 1U);
}

TEST(CoverageControl, RepeatedResetHasNoEffect) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kFull);
  RunControl(f, kStart, kScope);

  EXPECT_EQ(RunControl(f, kReset, kScope), kOk);
  EXPECT_EQ(RunControl(f, kReset, kScope), kOk);
  EXPECT_EQ(Cov(f).ResetCount(std::string(kScope), kToggle), 1U);
}

TEST(CoverageControl, ResetWithoutCoverageHasNoEffect) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kNone);

  EXPECT_EQ(RunControl(f, kReset, kScope), kOk);
  EXPECT_EQ(Cov(f).ResetCount(std::string(kScope), kToggle), 0U);
}

TEST(CoverageControl, UnknownScopeIsBadArgument) {
  SimFixture f;
  const std::string kMissing = "$root.tb.nonesuch";

  EXPECT_EQ(RunControl(f, kStart, kMissing), kError);
  EXPECT_EQ(RunControl(f, kStop, kMissing), kError);
  EXPECT_EQ(RunControl(f, kReset, kMissing), kError);
  EXPECT_EQ(RunControl(f, kCheck, kMissing), kError);

  EXPECT_FALSE(Cov(f).IsRegistered(kMissing));
  EXPECT_FALSE(Cov(f).IsCollecting(kMissing, kToggle));
}

TEST(CoverageControl, InvalidControlConstantIsBadArgument) {
  SimFixture f;
  Cov(f).SetAvailability(std::string(kScope), kToggle,
                         CoverageAvailability::kFull);

  EXPECT_EQ(RunControl(f, 99, kScope), kError);
  EXPECT_FALSE(Cov(f).IsCollecting(std::string(kScope), kToggle));
}

TEST(CoverageControl, MissingArgumentsIsBadArgument) {
  SimFixture f;
  auto* call = MkSysCall(f.arena, "$coverage_control", {});
  EXPECT_EQ(static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64()),
            kError);
}

int RunControlWithScopeDef(SimFixture& f, int control, int scope_def,
                           std::string_view scope) {
  auto* call = MkSysCall(
      f.arena, "$coverage_control",
      {MkInt(f.arena, static_cast<uint64_t>(control)), MkInt(f.arena, kToggle),
       MkInt(f.arena, static_cast<uint64_t>(scope_def)),
       MkStr(f.arena, scope)});
  return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
}

constexpr int kSvCovModule = 10;
constexpr int kSvCovHier = 11;

TEST(CoverageControl, HierReachesTheHierarchyBelowTheNamedInstance) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
  Cov(f).SetAvailability("top.dut.u1", kToggle, CoverageAvailability::kFull);
  Cov(f).SetAvailability("top.other", kToggle, CoverageAvailability::kFull);

  EXPECT_EQ(RunControlWithScopeDef(f, kStart, kSvCovHier, "top.dut"), kOk);

  EXPECT_TRUE(Cov(f).IsCollecting("top.dut", kToggle));
  EXPECT_TRUE(Cov(f).IsCollecting("top.dut.u1", kToggle));
  EXPECT_FALSE(Cov(f).IsCollecting("top.other", kToggle));
}

TEST(CoverageControl, ModuleReachesTheNamedInstanceAlone) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
  Cov(f).SetAvailability("top.dut.u1", kToggle, CoverageAvailability::kFull);

  EXPECT_EQ(RunControlWithScopeDef(f, kStart, kSvCovModule, "top.dut"), kOk);

  EXPECT_TRUE(Cov(f).IsCollecting("top.dut", kToggle));
  EXPECT_FALSE(Cov(f).IsCollecting("top.dut.u1", kToggle));
}

TEST(CoverageControl, APartlyCoverableHierarchyReportsPartial) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
  Cov(f).SetAvailability("top.dut.u1", kToggle, CoverageAvailability::kNone);

  EXPECT_EQ(RunControlWithScopeDef(f, kStart, kSvCovHier, "top.dut"), kPartial);
  EXPECT_EQ(RunControlWithScopeDef(f, kStart, kSvCovModule, "top.dut"), kOk);
}

TEST(CoverageControl, ADefinitionNameControlsEveryInstanceOfThatModule) {
  SimFixture f;
  Cov(f).SetAvailability("top.u1", kToggle, CoverageAvailability::kFull);
  Cov(f).SetModuleDefinition("top.u1", "leaf");
  Cov(f).SetAvailability("top.u2", kToggle, CoverageAvailability::kFull);
  Cov(f).SetModuleDefinition("top.u2", "leaf");
  Cov(f).SetAvailability("top.u2.inner", kToggle, CoverageAvailability::kFull);
  Cov(f).SetModuleDefinition("top.u2.inner", "other");

  EXPECT_EQ(RunControlWithScopeDef(f, kStart, kSvCovModule, "leaf"), kOk);

  EXPECT_TRUE(Cov(f).IsCollecting("top.u1", kToggle));
  EXPECT_TRUE(Cov(f).IsCollecting("top.u2", kToggle));
  EXPECT_FALSE(Cov(f).IsCollecting("top.u2.inner", kToggle));
}

TEST(CoverageControl, ADefinitionNameReportsTheStatusOfAllItsInstances) {
  SimFixture f;
  Cov(f).SetAvailability("top.u1", kToggle, CoverageAvailability::kFull);
  Cov(f).SetModuleDefinition("top.u1", "leaf");
  Cov(f).SetAvailability("top.u2", kToggle, CoverageAvailability::kNone);
  Cov(f).SetModuleDefinition("top.u2", "leaf");

  EXPECT_EQ(RunControlWithScopeDef(f, kCheck, kSvCovHier, "leaf"), kPartial);
  EXPECT_EQ(RunControlWithScopeDef(f, kCheck, kSvCovHier, "top.u1"), kOk);
}

TEST(CoverageControl, AnUnknownScopeDefinitionIsABadArgument) {
  SimFixture f;
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);

  EXPECT_EQ(RunControlWithScopeDef(f, kStart, 99, "top.dut"), kError);
  EXPECT_FALSE(Cov(f).IsCollecting("top.dut", kToggle));
}

std::string TwoFsmDesign(const std::string& body) {
  return "module leaf;\n"
         "  parameter [1:0] /* tool enum leaf_e */ A = 0, B = 1, C = 2;\n"
         "  /* tool state_vector st enum leaf_e */\n"
         "  logic [1:0] st;\n"
         "  initial st = A;\n"
         "endmodule\n"
         "module top;\n"
         "  parameter [1:0] /* tool enum top_e */ X = 0, Y = 1;\n"
         "  /* tool state_vector ts enum top_e */\n"
         "  logic [1:0] ts;\n"
         "  leaf u1();\n"
         "  string m;\n"
         "  int r1, r2, r3;\n"
         "  initial begin\n"
         "    ts = X; #1\n" +
         body +
         "    $display(\"%0d %0d %0d\", r1, r2, r3);\n"
         "  end\n"
         "endmodule\n";
}

TEST(CoverageControl, AnInstanceIsNamedByARootedHierarchicalPath) {
  SimFixture f;
  const std::string kOut = RunCapture(
      TwoFsmDesign("    r1 = $coverage_get_max(21, 10, $root.top);\n"
                   "    r2 = $coverage_get_max(21, 11, $root.top);\n"
                   "    r3 = $coverage_get_max(21, 11, $root.top.u1);\n"),
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "2 5 3\n");
}

TEST(CoverageControl, AnInstanceOfTheCallingScopeNeedsNoDot) {
  SimFixture f;
  const std::string kOut =
      RunCapture(TwoFsmDesign("    r1 = $coverage_get_max(21, 11, u1);\n"
                              "    r2 = $coverage_get_max(21, 11, top.u1);\n"
                              "    r3 = $coverage_control(3, 21, 10, u1);\n"),
                 f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "3 3 1\n");
}

TEST(CoverageControl, RootAloneNamesTheWholeDesign) {
  SimFixture f;
  const std::string kOut =
      RunCapture(TwoFsmDesign("    r1 = $coverage_control(3, 21, 11, $root);\n"
                              "    r2 = $coverage_get_max(21, 11, $root);\n"
                              "    r3 = $coverage_get(21, 11, $root);\n"),
                 f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "1 5 2\n");
}

TEST(CoverageControl, AStringVariableNamesWhatItHolds) {
  SimFixture f;
  const std::string kOut = RunCapture(
      TwoFsmDesign(
          "    m = \"leaf\";\n"
          "    r1 = $coverage_get_max(21, 11, m);\n"
          "    r2 = $coverage_get(21, 11, m);\n"
          "    m = \"top\";\n"
          "    r3 = $coverage_control(3, 21, 10, $sformatf(\"%s\", m));\n"),
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "3 1 1\n");
}

TEST(CoverageControl, AControlActsOnTheCoverageTypeItNames) {
  SimFixture f;
  const std::string kOut = RunCapture(
      TwoFsmDesign("    r1 = $coverage_control(3, 20, 10, \"top\");\n"
                   "    r2 = $coverage_control(1, 22, 11, \"top\");\n"
                   "    ts = Y; #1\n"
                   "    r3 = $coverage_get(21, 10, \"top\");\n"),
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "0 1 2\n");
}

TEST(CoverageControl, ARootedPathNamingNoInstanceIsABadArgument) {
  SimFixture f;
  Cov(f).SetModuleDefinition("top", "top");
  Cov(f).SetAvailability("top", kToggle, CoverageAvailability::kFull);
  Expr* nosuch = MkId(f.arena, "nosuch");
  nosuch->scope_prefix = "$root";
  auto run = [&f](Expr* scope) {
    auto* call = MkSysCall(f.arena, "$coverage_control",
                           {MkInt(f.arena, kCheck), MkInt(f.arena, kToggle),
                            MkInt(f.arena, 11), scope});
    return static_cast<int32_t>(EvalExpr(call, f.ctx, f.arena).ToUint64());
  };

  EXPECT_EQ(run(nosuch), kError);
  EXPECT_EQ(run(nullptr), kError);
}

TEST(CoverageControl, StopAndResetReportOkWhereCheckWouldNot) {
  SimFixture f;
  Cov(f).SetAvailability("top.none", kToggle, CoverageAvailability::kNone);
  Cov(f).SetAvailability("top.dut", kToggle, CoverageAvailability::kFull);
  Cov(f).SetAvailability("top.dut.u1", kToggle, CoverageAvailability::kNone);

  EXPECT_EQ(RunControlWithScopeDef(f, kCheck, kSvCovHier, "top.none"), kNoCov);
  EXPECT_EQ(RunControlWithScopeDef(f, kStop, kSvCovHier, "top.none"), kOk);
  EXPECT_EQ(RunControlWithScopeDef(f, kCheck, kSvCovHier, "top.dut"), kPartial);
  EXPECT_EQ(RunControlWithScopeDef(f, kStop, kSvCovHier, "top.dut"), kOk);
  EXPECT_EQ(RunControlWithScopeDef(f, kReset, kSvCovHier, "top.dut"), kOk);
}

std::string TwoMidDesign(const std::string& body) {
  return "module sub;\n"
         "  logic s = 0;\n"
         "endmodule\n"
         "module mid;\n"
         "  logic m = 0;\n"
         "  sub u();\n"
         "endmodule\n"
         "module top;\n"
         "  mid dut();\n"
         "  mid other();\n"
         "  int r1, r2;\n"
         "  task automatic flip_all();\n"
         "    #1 dut.m = 1; dut.u.s = 1; other.m = 1; other.u.s = 1;\n"
         "    #1 dut.m = 0; dut.u.s = 0; other.m = 0; other.u.s = 0;\n"
         "  endtask\n"
         "  initial begin\n" +
         body +
         "    #1 $display(\"%0d %0d | %0d %0d %0d %0d\", r1, r2,\n"
         "        $coverage_get(23, 10, dut), $coverage_get(23, 10, dut.u),\n"
         "        $coverage_get(23, 10, other),\n"
         "        $coverage_get(23, 10, other.u));\n"
         "  end\n"
         "endmodule\n";
}

std::string RunTwoMid(const std::string& body) {
  SimFixture f;
  std::string out = RunCapture(TwoMidDesign(body), f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

TEST(CoverageControl, AStartUnderHierOverAnInstancePathStartsItsSubtree) {
  EXPECT_EQ(RunTwoMid("    r1 = $coverage_control(1, 23, 11, $root);\n"
                      "    r2 = $coverage_control(0, 23, 11, top.dut);\n"
                      "    flip_all();\n"),
            "1 1 | 1 1 0 0\n");
}

TEST(CoverageControl, AStartUnderModuleOverAnInstancePathStartsItAlone) {
  EXPECT_EQ(RunTwoMid("    r1 = $coverage_control(1, 23, 11, $root);\n"
                      "    r2 = $coverage_control(0, 23, 10, dut);\n"
                      "    flip_all();\n"),
            "1 1 | 1 0 0 0\n");
}

TEST(CoverageControl, AStopUnderHierOverAnInstancePathKeepsWhatItCollected) {
  EXPECT_EQ(RunTwoMid("    dut.u.s = 1; other.u.s = 1;\n"
                      "    #1 dut.u.s = 0; other.u.s = 0;\n"
                      "    r1 = $coverage_control(1, 23, 11, dut);\n"
                      "    r2 = $coverage_control(1, 23, 11, dut);\n"
                      "    flip_all();\n"),
            "1 1 | 0 1 1 1\n");
}

TEST(CoverageControl, ACheckOfAStoppedScopeStillFindsItsCoverage) {
  EXPECT_EQ(RunTwoMid("    r1 = $coverage_control(1, 23, 11, $root);\n"
                      "    r2 = $coverage_control(3, 23, 11, dut);\n"
                      "    flip_all();\n"),
            "1 1 | 0 0 0 0\n");
}

TEST(CoverageControl, ADefinitionNameUnderHierStartsBelowEveryInstance) {
  EXPECT_EQ(RunTwoMid("    r1 = $coverage_control(1, 23, 11, $root);\n"
                      "    r2 = $coverage_control(0, 23, 11, \"mid\");\n"
                      "    flip_all();\n"),
            "1 1 | 1 1 1 1\n");
}

TEST(CoverageControl, ADefinitionNameUnderModuleStartsEveryInstanceAlone) {
  EXPECT_EQ(RunTwoMid("    r1 = $coverage_control(1, 23, 11, $root);\n"
                      "    r2 = $coverage_control(0, 23, 10, \"mid\");\n"
                      "    flip_all();\n"),
            "1 1 | 1 0 1 0\n");
}

TEST(CoverageControl, ADefinitionNameUnderHierStopsBelowEveryInstance) {
  EXPECT_EQ(RunTwoMid("    r1 = $coverage_control(1, 23, 11, \"mid\");\n"
                      "    r2 = $coverage_control(3, 23, 11, \"mid\");\n"
                      "    flip_all();\n"),
            "1 1 | 0 0 0 0\n");
}

TEST(CoverageControl, ADefinitionNameUnderHierResetsBelowEveryInstance) {
  EXPECT_EQ(RunTwoMid("    flip_all();\n"
                      "    r1 = $coverage_control(2, 23, 11, \"mid\");\n"
                      "    r2 = $coverage_get(23, 11, \"mid\");\n"),
            "1 0 | 0 0 0 0\n");
}

TEST(CoverageControl, ADefinitionNameUnderModuleResetsEveryInstanceAlone) {
  EXPECT_EQ(RunTwoMid("    flip_all();\n"
                      "    r1 = $coverage_control(2, 23, 10, \"mid\");\n"
                      "    r2 = 1;\n"),
            "1 1 | 0 1 0 1\n");
}

TEST(CoverageControl, DISABLED_AStringHoldingADottedPathIsADefinitionName) {
  EXPECT_EQ(
      RunTwoMid("    r1 = $coverage_control(3, 23, 11, \"top.dut\");\n"
                "    r2 = $coverage_control(1, 23, 11, \"$root.top.dut\");\n"
                "    flip_all();\n"),
      "-1 -1 | 1 1 1 1\n");
}

TEST(CoverageControl, TheSamePathUnquotedNamesTheInstance) {
  EXPECT_EQ(RunTwoMid("    r1 = $coverage_control(3, 23, 11, top.dut);\n"
                      "    r2 = $coverage_control(1, 23, 11, $root.top.dut);\n"
                      "    flip_all();\n"),
            "1 1 | 0 0 1 1\n");
}

TEST(CoverageControl, ARelativePathIsResolvedFromTheCallingScope) {
  SimFixture f;
  const std::string kOut = RunCapture(
      "module mid;\n"
      "  logic m;\n"
      "endmodule\n"
      "program p;\n"
      "  initial #1 $display(\"p %0d\", $coverage_control(3, 23, 10, "
      "top.dut));\n"
      "endprogram\n"
      "module top;\n"
      "  mid dut();\n"
      "  p pp();\n"
      "  class C;\n"
      "    function int ask();\n"
      "      return $coverage_get_max(23, 10, dut);\n"
      "    endfunction\n"
      "  endclass\n"
      "  function int ask();\n"
      "    return $coverage_get_max(23, 10, dut);\n"
      "  endfunction\n"
      "  task automatic tell();\n"
      "    $display(\"t %0d\", $coverage_control(3, 23, 10, dut));\n"
      "  endtask\n"
      "  initial begin\n"
      "    automatic C c = new;\n"
      "    $display(\"f %0d c %0d\", ask(), c.ask());\n"
      "    tell();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(kOut, "f 1 c 1\nt 1\np 1\n");
}

}  // namespace
