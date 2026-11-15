#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_expect_runs.h"

using namespace delta;

namespace {

constexpr const char* kPassingExpect =
    "expect (@(posedge clk) a) $display(\"pass at %0d\", $time);\n";

void PassesAt(const std::string& when, const std::string& body,
              const std::string& declarations, const std::string& before = "") {
  SimFixture f;
  std::string out = RunCapture(before + ExpectDesign(body, declarations), f);
  EXPECT_TRUE(f.diag.Diagnostics().empty()) << declarations << body;
  EXPECT_EQ(out, "pass at " + when + "\n$finish at time 210\n")
      << declarations << body;
}

TEST(ExpectPlacementRun, AStaticModuleTask) {
  PassesAt("25", "    st();\n",
           std::string("  task st();\n    ") + kPassingExpect + "  endtask\n");
}

TEST(ExpectPlacementRun, AModuleAlwaysProcedure) {
  PassesAt("25", "",
           std::string("  always @(posedge clk) if ($time == 15)\n    ") +
               kPassingExpect);
}

TEST(ExpectPlacementRun, EachForkBranchOfAnInitialProcedure) {
  for (const char* join : {"join", "join_any", "join_none"}) {
    PassesAt(
        "25",
        std::string("    fork\n      ") + kPassingExpect + "    " + join + "\n",
        "");
  }
}

TEST(ExpectPlacementRun, AForkJoinNoneInsideAFunction) {
  PassesAt("25", "    f();\n",
           std::string("  function void f();\n    fork\n      ") +
               kPassingExpect + "    join_none\n  endfunction\n");
}

TEST(ExpectPlacementRun, AClassMethodTask) {
  PassesAt("25", "    h.run();\n",
           std::string("  class C;\n    task run();\n      ") + kPassingExpect +
               "    endtask\n  endclass\n  C h = new;\n");
}

TEST(ExpectPlacementRun, APackageTask) {
  PassesAt("25", "    pk::pt();\n",
           "  always #5 pk::pclk = ~pk::pclk;\n"
           "  initial #22 pk::pa = 1;\n",
           "package pk;\n  logic pclk = 0, pa = 0;\n"
           "  task automatic pt();\n"
           "    expect (@(posedge pclk) pa) $display(\"pass at %0d\", $time);\n"
           "  endtask\nendpackage\n");
}

TEST(ExpectPlacementRun, ACompilationUnitTask) {
  PassesAt("25", "    ut();\n",
           "  always #5 uclk = ~uclk;\n"
           "  initial #22 ua = 1;\n",
           "logic uclk = 0, ua = 0;\n"
           "task automatic ut();\n"
           "  expect (@(posedge uclk) ua) $display(\"pass at %0d\", $time);\n"
           "endtask\n");
}

TEST(ExpectPlacementRun, AnInterfaceInitialProcedure) {
  PassesAt("25", "",
           std::string("  interface ifc;\n    initial begin\n      #20;\n"
                       "      ") +
               kPassingExpect + "    end\n  endinterface\n  ifc u();\n");
}

TEST(ExpectPlacementRun, AnInterfaceTask) {
  PassesAt("25", "    u.it();\n",
           std::string("  interface ifc;\n    task it();\n      ") +
               kPassingExpect + "    endtask\n  endinterface\n  ifc u();\n");
}

TEST(ExpectPlacementRun, AProgramInitialProcedure) {
  PassesAt("25", "",
           std::string("  program pr;\n    initial begin\n      #20;\n"
                       "      ") +
               kPassingExpect + "      #200;\n    end\n  endprogram\n");
}

TEST(ExpectPlacementRun, AProgramTask) {
  PassesAt("25", "",
           std::string("  program pr;\n    task pt();\n      ") +
               kPassingExpect +
               "    endtask\n    initial begin\n      #20;\n      pt();\n"
               "      #200;\n    end\n  endprogram\n");
}

TEST(ExpectPlacementRun, AGenerateBlockInitialProcedure) {
  PassesAt("25", "",
           std::string("  if (1) begin : g\n    initial begin\n      #20;\n"
                       "      ") +
               kPassingExpect + "    end\n  end\n");
}

std::string ExpectOn(const std::string& condition) {
  return "expect (@(posedge clk) " + condition +
         ") $display(\"pass at %0d\", $time);\n"
         "      else $display(\"fail at %0d\", $time);\n";
}

TEST(ExpectAutomaticReadRun, ALocalOfAnAutomaticTask) {
  PassesAt("25", "    t();\n",
           "  task automatic t();\n    int v = 2;\n    " +
               ExpectOn("data == v") + "  endtask\n");
}

TEST(ExpectAutomaticReadRun, AnAutomaticInABlockOfAnInitialProcedure) {
  PassesAt("25",
           "    begin\n      automatic int v = 2;\n      " +
               ExpectOn("data == v") + "    end\n",
           "");
}

TEST(ExpectAutomaticReadRun, AForLoopVariableAtEachIteration) {
  SimFixture f;
  std::string out = RunCapture(
      ExpectDesign("    for (int i = 2; i <= 3; i++)\n"
                   "      expect (@(posedge clk) data == i)\n"
                   "        $display(\"i=%0d pass at %0d\", i, $time);\n"
                   "        else $display(\"i=%0d fail at %0d\", i, $time);\n"),
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out, "i=2 pass at 25\ni=3 pass at 35\n$finish at time 210\n");
}

TEST(ExpectAutomaticReadRun, AnAutomaticInAForkBranch) {
  PassesAt("25",
           "    fork\n      begin\n        automatic int v = 2;\n        " +
               ExpectOn("data == v") + "      end\n    join\n",
           "");
}

TEST(ExpectAutomaticReadRun, EachSpawnedBranchReadsItsOwnIterationsCopy) {
  SimFixture f;
  std::string out = RunCapture(
      ExpectDesign("    for (int i = 2; i <= 4; i++)\n"
                   "      fork\n"
                   "        automatic int k = i;\n"
                   "        expect (@(posedge clk) ##[0:5] data == k)\n"
                   "          $display(\"k=%0d pass at %0d\", k, $time);\n"
                   "      join_none\n"),
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out,
            "k=2 pass at 25\nk=3 pass at 35\nk=4 pass at 45\n"
            "$finish at time 210\n");
}

constexpr const char* kCounter =
    "  int cv = 0;\n  always @(posedge clk) cv <= cv + 1;\n";

TEST(ExpectAutomaticReadRun,
     DISABLED_AClassMethodArgumentBesideAStaticOperand) {
  PassesAt("25", "    h.t(2);\n",
           std::string(kCounter) + "  class C;\n    task t(int v);\n      " +
               ExpectOn("cv == v") + "    endtask\n  endclass\n  C h = new;\n");
}

TEST(ExpectAutomaticReadRun, AnInterfaceAutomaticTaskArgument) {
  PassesAt("25", "    u.it(2);\n",
           "  interface ifc;\n    task automatic it(int v);\n      " +
               ExpectOn("data == v") +
               "    endtask\n  endinterface\n  ifc u();\n");
}

TEST(ExpectAutomaticReadRun, AProgramAutomaticTaskArgument) {
  PassesAt("25", "",
           "  program pr;\n    task automatic pt(int v);\n      " +
               ExpectOn("data == v") +
               "    endtask\n    initial begin\n      #20;\n      pt(2);\n"
               "      #200;\n    end\n  endprogram\n");
}

TEST(ExpectAutomaticReadRun, AnArgumentPassedToANamedPropertysFormal) {
  PassesAt("25", "    tp(2);\n",
           "  property pw(int x);\n    @(posedge clk) data == x;\n"
           "  endproperty\n"
           "  task automatic tp(int v);\n"
           "    expect (pw(v)) $display(\"pass at %0d\", $time);\n"
           "      else $display(\"fail at %0d\", $time);\n"
           "  endtask\n");
}

constexpr const char* kAdvanceSv =
    "    fork\n      forever @(posedge clk) sv <= sv + 1;\n    join_none\n";

TEST(ExpectStaticReadRun, DISABLED_ALocalOfAStaticTask) {
  PassesAt("25", "    st();\n",
           std::string("  task st();\n    int sv;\n") + kAdvanceSv + "    " +
               ExpectOn("sv == 0") + "  endtask\n");
}

TEST(ExpectStaticReadRun, DISABLED_AStaticLocalOfAnAutomaticTask) {
  PassesAt("25", "    ta();\n",
           std::string("  task automatic ta();\n    static int sv = 0;\n") +
               kAdvanceSv + "    " + ExpectOn("sv == 0") + "  endtask\n");
}

TEST(ExpectStaticReadRun, AnInterfaceVariableFromItsInitial) {
  PassesAt("25", "",
           "  interface ifc;\n    int iv = 0;\n"
           "    always @(posedge clk) iv <= iv + 1;\n"
           "    initial begin\n      #20;\n      " +
               ExpectOn("iv == 2") + "    end\n  endinterface\n  ifc u();\n");
}

TEST(ExpectStaticReadRun, AnInterfaceVariableFromItsAutomaticTask) {
  PassesAt("25", "    u.it();\n",
           "  interface ifc;\n    int iv = 0;\n"
           "    always @(posedge clk) iv <= iv + 1;\n"
           "    task automatic it();\n      " +
               ExpectOn("iv == 2") +
               "    endtask\n  endinterface\n  ifc u();\n");
}

TEST(ExpectStaticReadRun, AProgramVariableFromItsInitial) {
  PassesAt("25", "",
           "  program pr;\n    int pv;\n    assign pv = data;\n"
           "    initial begin\n      #20;\n      " +
               ExpectOn("pv == 2") + "      #200;\n    end\n  endprogram\n");
}

TEST(ExpectStaticReadRun, AProgramVariableFromItsAutomaticTask) {
  PassesAt("25", "",
           "  program pr;\n    int pv;\n    assign pv = data;\n"
           "    task automatic pt();\n      " +
               ExpectOn("pv == 2") +
               "    endtask\n    initial begin\n      #20;\n      pt();\n"
               "      #200;\n    end\n  endprogram\n");
}

TEST(ExpectStaticReadRun, ACompilationUnitVariable) {
  PassesAt("25", "    " + ExpectOn("uv == 2"),
           "  always @(posedge clk) uv <= uv + 1;\n", "int uv = 0;\n");
}

constexpr const char* kPackageCounter =
    "package pk;\n  int pv = 0;\nendpackage\n";

TEST(ExpectStaticReadRun, AnImportedPackageVariable) {
  PassesAt("25", "    " + ExpectOn("pv == 2"),
           "  import pk::*;\n  always @(posedge clk) pv <= pv + 1;\n",
           kPackageCounter);
}

TEST(ExpectStaticReadRun, DISABLED_APackageVariableWrittenWithItsPrefix) {
  PassesAt("25", "    " + ExpectOn("pk::pv == 2"),
           "  always @(posedge clk) pk::pv <= pk::pv + 1;\n", kPackageCounter);
}

TEST(ExpectStaticReadRun, DISABLED_AGenerateBlockVariableFromItsInitial) {
  PassesAt("25", "",
           "  if (1) begin : g\n    int gv = 0;\n"
           "    always @(posedge clk) gv <= gv + 1;\n"
           "    initial begin\n      #20;\n      " +
               ExpectOn("gv == 2") + "    end\n  end\n");
}

TEST(ExpectStaticReadRun, DISABLED_AModuleVariableFromAClassMethodTask) {
  PassesAt("25", "    h.t();\n",
           std::string(kCounter) + "  class C;\n    task t();\n      " +
               ExpectOn("cv == 2") + "    endtask\n  endclass\n  C h = new;\n");
}

constexpr const char* kStaticProperty =
    "  class C;\n    static int sp = 0;\n    task t();\n      "
    "expect (@(posedge clk) sp == 2) $display(\"pass at %0d\", $time);\n"
    "        else $display(\"fail at %0d\", $time);\n"
    "    endtask\n  endclass\n  C h = new;\n"
    "  always @(posedge clk) C::sp <= C::sp + 1;\n";

TEST(ExpectStaticReadRun, DISABLED_AStaticClassPropertyFromAMethod) {
  PassesAt("25", "    h.t();\n", kStaticProperty);
}

TEST(ExpectStaticReadRun, DISABLED_AStaticClassPropertyByItsClassName) {
  PassesAt("25", "    " + ExpectOn("C::sp == 2"), kStaticProperty);
}

}  // namespace
