#include <gtest/gtest.h>

#include <string>

#include "helpers_placed_assertion_runs.h"

using namespace delta;

namespace {

std::string RunLines(const std::string& src) {
  return PlacedSortedVerdicts(RunPlaced(src).lines);
}

const char* const kSignals =
    "  logic clk1 = 0, clk2 = 0, rst1 = 1, rst2 = 0, a = 0;\n"
    "  always #5 clk1 = ~clk1;\n"
    "  always #7 clk2 = ~clk2;\n"
    "  initial begin #18 rst1 = 0; #32 $finish; end\n";

const char* const kDefaults1 =
    "  default clocking @(posedge clk1); endclocking\n"
    "  default disable iff rst1;\n";

const char* const kDefaults2 =
    "  default clocking @(posedge clk2); endclocking\n"
    "  default disable iff rst2;\n";

std::string Checker(const std::string& name, const std::string& own) {
  return "  checker " + name + "(logic x);\n" + own +
         "    a1: assert property (x) else $display(\"%0t\", $time);\n"
         "  endchecker\n";
}

const char* const kOnClk1AfterRst1 = "25\n35\n45\n";
const char* const kOnClk2AfterRst1 = "21\n35\n49\n";
const char* const kOnClk1 = "15\n25\n35\n45\n5\n";
const char* const kOnClk2 = "21\n35\n49\n7\n";

std::string InTop(const std::string& items) {
  return "module t;\n" + std::string(kSignals) + items + "endmodule\n";
}

TEST(CheckerInheritedDefaultsRun, TheModulesDefaultDisableIff) {
  EXPECT_EQ(RunLines(InTop(kDefaults1 + Checker("c1", "") + "  c1 u(a);\n")),
            kOnClk1AfterRst1);
}

TEST(CheckerInheritedDefaultsRun, ItsOwnClockingKeepsTheModulesDisable) {
  EXPECT_EQ(RunLines(InTop(kDefaults1 +
                           Checker("c1",
                                   "    default clocking @(posedge clk2); "
                                   "endclocking\n") +
                           "  c1 u(a);\n")),
            kOnClk2AfterRst1);
}

TEST(CheckerInheritedDefaultsRun, ItsOwnDisableKeepsTheModulesClocking) {
  EXPECT_EQ(RunLines(InTop(kDefaults1 +
                           Checker("c1", "    default disable iff rst2;\n") +
                           "  c1 u(a);\n")),
            kOnClk1);
}

TEST(CheckerInheritedDefaultsRun, ItsOwnDefaultsReplaceBoth) {
  EXPECT_EQ(
      RunLines(InTop(kDefaults1 + Checker("c2", kDefaults2) + "  c2 u(a);\n")),
      kOnClk2);
}

TEST(CheckerInheritedDefaultsRun, AnEnclosingCheckersOwnDefaults) {
  EXPECT_EQ(RunLines(InTop(kDefaults1 + std::string("  checker o(logic x);\n") +
                           kDefaults2 + Checker("c1", "") +
                           "    c1 u(x);\n  endchecker\n  o uo(a);\n")),
            kOnClk2);
}

TEST(CheckerInheritedDefaultsRun, ThroughAnEnclosingCheckerWithoutDefaults) {
  EXPECT_EQ(RunLines(InTop(kDefaults1 + std::string("  checker o(logic x);\n") +
                           Checker("c1", "") +
                           "    c1 u(x);\n  endchecker\n  o uo(a);\n")),
            kOnClk1AfterRst1);
}

std::string InContainer(const std::string& keyword, const std::string& name,
                        const std::string& body) {
  return keyword + " " + name + "(input logic clk1, clk2, rst1, rst2, a);\n" +
         body + "end" + keyword + "\n";
}

TEST(CheckerInheritedDefaultsRun, AnInterfacesDefaultsNotItsInstantiators) {
  EXPECT_EQ(
      RunLines(InContainer("interface", "ifc",
                           kDefaults1 + Checker("c1", "") + "  c1 u(a);\n") +
               InTop(kDefaults2 +
                     std::string("  ifc i(clk1, clk2, rst1, rst2, a);\n"))),
      kOnClk1AfterRst1);
}

TEST(CheckerInheritedDefaultsRun, AProgramsDefaults) {
  EXPECT_EQ(
      RunLines(InContainer("program", "prg",
                           kDefaults1 + Checker("c1", "") + "  c1 u(a);\n") +
               InTop(kDefaults2 +
                     std::string("  prg p(clk1, clk2, rst1, rst2, a);\n"))),
      kOnClk1AfterRst1);
}

TEST(CheckerInheritedDefaultsRun, DISABLED_AGenerateBlocksDefaults) {
  EXPECT_EQ(
      RunLines(InTop(kDefaults2 + std::string("  if (1) begin : g\n") +
                     kDefaults1 + Checker("c1", "") + "    c1 u(a);\n  end\n")),
      kOnClk1AfterRst1);
}

TEST(CheckerInheritedDefaultsRun,
     DISABLED_ANestedModuleWithItsOwnDefaultsUsesTheDeclarers) {
  EXPECT_EQ(
      RunLines(InTop(kDefaults1 + Checker("c1", "") + "  module inner;\n" +
                     kDefaults2 + "    c1 u(a);\n  endmodule\n  inner i();\n")),
      kOnClk1AfterRst1);
}

TEST(CheckerInheritedDefaultsRun,
     DISABLED_ANestedModuleWithoutDefaultsUsesTheDeclarers) {
  EXPECT_EQ(RunLines(InTop(kDefaults1 + Checker("c1", "") +
                           "  module inner;\n    c1 u(a);\n  endmodule\n"
                           "  inner i();\n")),
            kOnClk1AfterRst1);
}

TEST(CheckerInheritedDefaultsRun, DISABLED_AGenerateBlocksDisableIsNotTaken) {
  EXPECT_EQ(RunLines(InTop(kDefaults1 + Checker("c1", "") +
                           "  if (1) begin : g\n"
                           "    default disable iff 1'b1;\n"
                           "    c1 u(a);\n  end\n")),
            kOnClk1AfterRst1);
}

const char* const kOwnClockChecker =
    "  checker cu(logic clk, logic x);\n"
    "    default clocking @(posedge clk); endclocking\n"
    "    a1: assert property (x) else $display(\"%0t\", $time);\n"
    "  endchecker\n";

TEST(CheckerInheritedDefaultsRun, AUnitCheckerIsNotDisabledByTheModule) {
  EXPECT_EQ(RunLines(kOwnClockChecker +
                     InTop(kDefaults1 + std::string("  cu u(clk1, a);\n"))),
            kOnClk1);
}

TEST(CheckerInheritedDefaultsRun, APackageCheckerIsNotDisabledByTheModule) {
  EXPECT_EQ(RunLines("package pk;\n" + std::string(kOwnClockChecker) +
                     "endpackage\n" +
                     InTop(kDefaults1 + std::string("  pk::cu u(clk1, a);\n"))),
            kOnClk1);
}

TEST(CheckerLocalDeclarationsRun, EachCheckerKeepsItsOwnTypedef) {
  EXPECT_EQ(RunLines("module t;\n"
                     "  typedef logic [1:0] w_t;\n"
                     "  w_t mw;\n"
                     "  checker c1;\n"
                     "    typedef logic [3:0] w_t;\n"
                     "    w_t w;\n"
                     "    int nb = $bits(w);\n"
                     "  endchecker\n"
                     "  checker c2;\n"
                     "    typedef logic [11:0] w_t;\n"
                     "    w_t w;\n"
                     "    int nb = $bits(w);\n"
                     "  endchecker\n"
                     "  c1 u1();\n"
                     "  c2 u2();\n"
                     "  initial #1 $display(\"%0d %0d %0d\", $bits(mw), u1.nb, "
                     "u2.nb);\n"
                     "endmodule\n"),
            "2 4 12\n");
}

const char* const kShadowingChecker =
    "  checker chk(logic clk);\n"
    "    int x = 3;\n"
    "    always_ff @(posedge clk) $display(\"chk %0d\", x);\n"
    "  endchecker\n";

const char* const kClock =
    "  logic clk = 0;\n"
    "  always #5 clk = ~clk;\n"
    "  initial #8 $finish;\n";

TEST(CheckerLocalDeclarationsRun, ItsVariableHidesTheModules) {
  EXPECT_EQ(RunLines(std::string("module t;\n  int x = 7;\n") + kClock +
                     kShadowingChecker +
                     "  chk u(clk);\n"
                     "  initial #6 $display(\"mod %0d\", x);\n"
                     "endmodule\n"),
            "chk 3\nmod 7\n");
}

TEST(CheckerLocalDeclarationsRun, ItsTypedefHidesTheModules) {
  EXPECT_EQ(RunLines("module t;\n"
                     "  typedef logic [1:0] w_t;\n"
                     "  w_t mw;\n"
                     "  checker chk;\n"
                     "    typedef logic [5:0] w_t;\n"
                     "    w_t w;\n"
                     "    int nb = $bits(w);\n"
                     "  endchecker\n"
                     "  chk u();\n"
                     "  initial #1 $display(\"%0d %0d\", $bits(mw), u.nb);\n"
                     "endmodule\n"),
            "2 6\n");
}

TEST(CheckerLocalDeclarationsRun, ItsDeclarationsHideTheCompilationUnits) {
  EXPECT_EQ(RunLines("typedef logic [2:0] w_t;\n"
                     "int x = 9;\n"
                     "module t;\n"
                     "  checker chk;\n"
                     "    typedef logic [4:0] w_t;\n"
                     "    int x = 3;\n"
                     "    w_t w;\n"
                     "    int nb = $bits(w);\n"
                     "    int nx = x;\n"
                     "  endchecker\n"
                     "  chk u();\n"
                     "  initial #1 $display(\"%0d %0d %0d\", u.nb, u.nx, x);\n"
                     "endmodule\n"),
            "5 3 9\n");
}

TEST(CheckerLocalDeclarationsRun, ItsEnumConstantHidesAnEnclosingName) {
  EXPECT_EQ(
      RunLines("module t;\n"
               "  parameter int K = 1;\n"
               "  typedef enum int {Z = 7} me_t;\n"
               "  checker chk;\n"
               "    typedef enum int {K = 5} ke_t;\n"
               "    typedef enum int {Z = 2} ce_t;\n"
               "    int kv = K;\n"
               "    int zv = Z;\n"
               "  endchecker\n"
               "  chk u();\n"
               "  initial #1 $display(\"%0d %0d %0d %0d\", u.kv, u.zv, K, "
               "Z);\n"
               "endmodule\n"),
      "5 2 1 7\n");
}

std::string ShadowContainer(const std::string& keyword,
                            const std::string& name) {
  return keyword + " " + name + "(input logic clk);\n  int x = 7;\n" +
         kShadowingChecker + "  chk u(clk);\nend" + keyword + "\n";
}

std::string ShadowTop(const std::string& items) {
  return "module t;\n" + std::string(kClock) + items + "endmodule\n";
}

TEST(CheckerLocalDeclarationsRun, ItsVariableHidesAnInterfacesAndAPrograms) {
  EXPECT_EQ(RunLines(ShadowContainer("interface", "ifc") +
                     ShadowTop("  ifc i(clk);\n")),
            "chk 3\n");
  EXPECT_EQ(RunLines(ShadowContainer("program", "prg") +
                     ShadowTop("  prg p(clk);\n")),
            "chk 3\n");
}

TEST(CheckerLocalDeclarationsRun, ItsVariableHidesAnOuterCheckers) {
  EXPECT_EQ(
      RunLines(ShadowContainer("checker", "o") + ShadowTop("  o uo(clk);\n")),
      "chk 3\n");
}

TEST(CheckerLocalDeclarationsRun, ItsVariableHidesAPackagesAndTheUnits) {
  EXPECT_EQ(
      RunLines(std::string("package pk;\n  int x = 7;\n") + kShadowingChecker +
               "endpackage\n" + ShadowTop("  pk::chk u(clk);\n")),
      "chk 3\n");
  EXPECT_EQ(RunLines(std::string("int x = 7;\n") + kShadowingChecker +
                     ShadowTop("  chk u(clk);\n")),
            "chk 3\n");
}

TEST(CheckerLocalDeclarationsRun, DISABLED_ItsVariableHidesAGenerateBlocks) {
  EXPECT_EQ(
      RunLines(ShadowTop(std::string("  if (1) begin : g\n    int x = 7;\n") +
                         kShadowingChecker + "    chk u(clk);\n  end\n")),
      "chk 3\n");
}

}  // namespace
