#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

const char kSay[] =
    "  function void say(input string s); $display(\"%0t %s\", $time, s); "
    "endfunction\n";

std::string Module(const std::string& items, const std::string& outside = "") {
  return outside + "module t;\n  logic a = 1;\n  event never;\n" + kSay +
         items + "endmodule\n";
}

std::string Captured(const std::string& src) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

std::string InOwnProcedure(const std::string& assertion,
                           const std::string& disable) {
  return Module("  initial begin : r\n    k: " + assertion + ";\n" + disable +
                "    say(\"after\");\n  end\n");
}

TEST(DisableSpecificAssertionLive, EveryKindIsCancelledByItsLabel) {
  for (const char* assertion :
       {"assert final (0) else say(\"k\")", "assume #0 (0) else say(\"k\")",
        "assume final (0) else say(\"k\")", "cover #0 (1) say(\"k\")",
        "cover final (1) say(\"k\")"}) {
    EXPECT_EQ(Captured(InOwnProcedure(assertion, "    disable k;\n")),
              "0 after\n")
        << assertion;
    EXPECT_EQ(Captured(InOwnProcedure(assertion, "")), "0 after\n0 k\n")
        << assertion;
  }
}

TEST(DisableSpecificAssertionLive, ADefaultErrorReportIsCancelledByItsLabel) {
  for (const char* assertion : {"assert #0 (0)", "assert final (0)"}) {
    SimFixture f;
    EXPECT_EQ(RunCapture(InOwnProcedure(assertion, "    disable k;\n"), f),
              "0 after\n")
        << assertion;
    EXPECT_EQ(f.ctx.LastSeverity(), "") << assertion;
    SimFixture g;
    RunCapture(InOwnProcedure(assertion, ""), g);
    EXPECT_EQ(g.ctx.LastSeverity(), "ERROR") << assertion;
  }
}

TEST(DisableSpecificAssertionLive, EveryExecutionInTheStepIsCancelled) {
  const std::string kLoop =
      "  initial begin : r\n"
      "    for (int i = 0; i < 3; i++)\n"
      "      m1: assert #0 (0) else say($sformatf(\"m1 %0d\", i));\n";
  EXPECT_EQ(Captured(Module(kLoop + "    disable m1;\n  end\n")), "");
  EXPECT_EQ(Captured(Module(kLoop + "  end\n")), "0 m1 0\n0 m1 1\n0 m1 2\n");
}

TEST(DisableSpecificAssertionLive, HierarchicalNamesFromTheSameProcess) {
  EXPECT_EQ(Captured(Module("  initial begin : r1\n"
                            "    k1: assert #0 (0) else say(\"k1\");\n"
                            "    k2: assert #0 (0) else say(\"k2\");\n"
                            "    k3: assert #0 (0) else say(\"k3\");\n"
                            "    disable r1.k1;\n"
                            "    disable t.r1.k2;\n"
                            "  end\n")),
            "0 k3\n");
}

TEST(DisableSpecificAssertionLive,
     DISABLED_ADisableFromAnotherProcessCancelsAndLeavesItRunning) {
  EXPECT_EQ(Captured(Module("  initial begin : r1\n"
                            "    k1: assert #0 (0) else say(\"k1\");\n"
                            "    @(never);\n"
                            "    say(\"r1 resumed\");\n"
                            "  end\n"
                            "  initial #0 disable r1.k1;\n"
                            "  initial #1 -> never;\n")),
            "1 r1 resumed\n");
}

TEST(DisableSpecificAssertionLive,
     DISABLED_AFunctionsAssertionIsCancelledInEveryCallersQueue) {
  EXPECT_EQ(Captured(Module("  function void f;\n"
                            "    fa: assert #0 (0) else say(\"fa\");\n"
                            "  endfunction\n"
                            "  initial begin : p1 f(); @(never); end\n"
                            "  initial begin : p2 f(); @(never); end\n"
                            "  initial #0 disable f.fa;\n")),
            "");
}

TEST(DisableSpecificAssertionLive, AModuleTasksAssertionIsCancelled) {
  const std::string kTask =
      "  task tk;\n"
      "    ta: assert #0 (0) else say(\"ta\");\n";
  EXPECT_EQ(
      Captured(Module(kTask + "    disable ta;\n  endtask\n  initial tk();\n")),
      "");
  EXPECT_EQ(Captured(Module(kTask + "  endtask\n  initial tk();\n")), "0 ta\n");
}

TEST(DisableSpecificAssertionLive,
     DISABLED_AModuleFunctionsAssertionIsCancelled) {
  EXPECT_EQ(Captured(Module("  bit r;\n"
                            "  function bit fn(input logic p);\n"
                            "    fa: assert #0 (p) else say(\"fa\");\n"
                            "    disable fa;\n"
                            "    return p;\n"
                            "  endfunction\n"
                            "  initial begin : b1 r = fn(0); @(never); end\n")),
            "");
}

const char kClass[] =
    "class C;\n"
    "  function void say(input string s); $display(\"%0t %s\", $time, s); "
    "endfunction\n";

TEST(DisableSpecificAssertionLive, AClassTasksAssertionIsCancelled) {
  EXPECT_EQ(Captured(Module("  C c = new;\n  initial c.run();\n",
                            std::string(kClass) +
                                "  task run;\n"
                                "    ca: assert #0 (0) else say(\"ca\");\n"
                                "    disable ca;\n"
                                "    say(\"after\");\n"
                                "  endtask\n"
                                "endclass\n")),
            "0 after\n");
}

TEST(DisableSpecificAssertionLive,
     DISABLED_AClassFunctionsAssertionIsCancelled) {
  EXPECT_EQ(Captured(Module("  C c = new;\n  initial c.m();\n",
                            std::string(kClass) +
                                "  function void m;\n"
                                "    ca: assert #0 (0) else say(\"ca\");\n"
                                "    disable ca;\n"
                                "    say(\"after\");\n"
                                "  endfunction\n"
                                "endclass\n")),
            "0 after\n");
}

TEST(DisableSpecificAssertionLive, AProgramsAssertionIsCancelled) {
  EXPECT_EQ(Captured(std::string("program p;\n") + kSay +
                     "  initial begin : r\n"
                     "    k: assert #0 (0) else say(\"k\");\n"
                     "    disable k;\n"
                     "    say(\"after\");\n"
                     "  end\n"
                     "endprogram\n"),
            "0 after\n");
}

TEST(DisableSpecificAssertionLive, WithoutADisableEachPlaceReportsOnce) {
  EXPECT_EQ(Captured(Module("  initial begin : r1\n"
                            "    k1: assert #0 (0) else say(\"k1\");\n"
                            "    @(never);\n"
                            "  end\n")),
            "0 k1\n");
  EXPECT_EQ(Captured(Module("  function void f;\n"
                            "    fa: assert #0 (0) else say(\"fa\");\n"
                            "  endfunction\n"
                            "  initial begin : p1 f(); @(never); end\n"
                            "  initial begin : p2 f(); @(never); end\n")),
            "0 fa\n0 fa\n");
  EXPECT_EQ(
      Captured(Module("  C c = new;\n  initial begin c.m(); c.run(); end\n",
                      std::string(kClass) +
                          "  function void m;\n"
                          "    cf: assert #0 (0) else say(\"cf\");\n"
                          "  endfunction\n"
                          "  task run;\n"
                          "    ct: assert #0 (0) else say(\"ct\");\n"
                          "  endtask\n"
                          "endclass\n")),
      "0 cf\n0 ct\n");
  EXPECT_EQ(Captured(std::string("program p;\n") + kSay +
                     "  initial begin : r\n"
                     "    k: assert #0 (0) else say(\"k\");\n"
                     "  end\n"
                     "endprogram\n"),
            "0 k\n");
}

struct StaticPlace {
  const char* outside;
  const char* items;
  const char* target;
  const char* name;
};

const StaticPlace kStaticPlaces[] = {
    {"", "  sa: assert #0 (a == 1) else say(\"sa\");\n", "sa", "sa"},
    {"module sub(input logic a);\n"
     "  ma: assert #0 (a == 1) else $display(\"%0t ma\", $time);\n"
     "endmodule\n",
     "  sub u1(a);\n", "u1.ma", "ma"},
    {"interface ifc(input logic a);\n"
     "  ia: assert #0 (a == 1) else $display(\"%0t ia\", $time);\n"
     "endinterface\n",
     "  ifc i1(a);\n", "i1.ia", "ia"},
    {"",
     "  if (1) begin : g\n    ga: assert #0 (a == 1) else say(\"ga\");\n"
     "  end\n",
     "g.ga", "ga"},
    {"checker chk(logic a);\n"
     "  ca: assert #0 (a == 1) else $display(\"%0t ca\", $time);\n"
     "endchecker\n",
     "  chk c1(a);\n", "c1.ca", "ca"},
};

std::string StaticRun(const StaticPlace& p, const std::string& disable) {
  return Captured(Module(std::string(p.items) + "  initial begin\n" +
                             "    #1 a = 0;\n" + disable + "  end\n",
                         p.outside));
}

TEST(DisableSpecificAssertionLive, AStaticAssertionWithoutADisableReports) {
  for (const auto& p : kStaticPlaces) {
    EXPECT_EQ(StaticRun(p, ""), std::string("1 ") + p.name + "\n") << p.target;
  }
}

TEST(DisableSpecificAssertionLive,
     DISABLED_AStaticAssertionIsCancelledWhereverItStands) {
  for (const auto& p : kStaticPlaces) {
    EXPECT_EQ(StaticRun(p, std::string("    #0 disable ") + p.target + ";\n"),
              "")
        << p.target;
  }
}

}  // namespace
