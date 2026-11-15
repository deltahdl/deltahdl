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

}  // namespace
