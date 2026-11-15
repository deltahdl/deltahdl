#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_clock_resolution_runs.h"
#include "helpers_report_times.h"

using namespace delta;

namespace {

constexpr const char* kBlocks =
    "  default clocking pcb @(posedge clk);\n"
    "    property qp; a |=> !b; endproperty\n"
    "    sequence sp; a ##1 b; endsequence\n"
    "  endclocking\n"
    "  clocking ncb @(negedge clk);\n"
    "    property qn; a |=> !b; endproperty\n"
    "    sequence sn; a ##1 b; endsequence\n"
    "  endclocking\n"
    "  property q1; a |=> !b; endproperty\n"
    "  sequence s1; a ##1 b; endsequence\n"
    "  sequence sf; !a ##1 !b; endsequence\n";

struct Scope {
  const char* keyword;
  const char* name;
  const char* procedure;
};

std::string ScopeDesign(const Scope& scope, const std::string& items) {
  std::string kw = scope.keyword;
  return ClockResolutionDesign(
      kw + " " + scope.name + "(input logic a, b, clk);\n" + kBlocks + items +
          "end" + kw + "\n",
      std::string("  ") + scope.name + " u1(a, b, clk);\n");
}

std::string RunScope(const Scope& scope, const std::string& items,
                     SimFixture& f) {
  return RunCapture(ScopeDesign(scope, items), f);
}

constexpr Scope kModule{"module", "m", "  always @(negedge clk) begin\n"};
constexpr Scope kInterface{"interface", "ifc",
                           "  always @(negedge clk) begin\n"};
constexpr Scope kChecker{"checker", "chk",
                         "  always_ff @(negedge clk) begin\n"};
constexpr Scope kProgram{"program", "prg", ""};

void ExpectExplicitClockSupersedes(const Scope& scope) {
  SimFixture f;
  std::string out =
      RunScope(scope,
               Failing("x1", "@(negedge clk) q1") +
                   Failing("x3", "@(negedge clk) q1", "assume") +
                   Covering("x2", "@(negedge clk) s1") +
                   Covering("x4", "@(negedge clk) s1", "cover sequence") +
                   Failing("x5", "@(negedge clk) sf") +
                   "  x6: restrict property (@(negedge clk) q1);\n",
               f);
  EXPECT_TRUE(f.diag.Diagnostics().empty()) << scope.keyword;
  EXPECT_EQ(ReportTimes(out, "x1"), "30") << scope.keyword;
  EXPECT_EQ(ReportTimes(out, "x2"), "30") << scope.keyword;
  EXPECT_EQ(ReportTimes(out, "x3"), "30") << scope.keyword;
  EXPECT_EQ(ReportTimes(out, "x4"), "30") << scope.keyword;
  EXPECT_EQ(ReportTimes(out, "x5"), "20") << scope.keyword;
}

void ExpectBlocksClockTheirDeclarations(const Scope& scope) {
  SimFixture f;
  std::string out =
      RunScope(scope,
               Failing("b1", "pcb.qp") + Covering("b2", "pcb.sp") +
                   Failing("n1", "ncb.qn") + Covering("n2", "ncb.sn"),
               f);
  EXPECT_TRUE(f.diag.Diagnostics().empty()) << scope.keyword;
  EXPECT_EQ(ReportTimes(out, "b1"), "25") << scope.keyword;
  EXPECT_EQ(ReportTimes(out, "b2"), "25") << scope.keyword;
  EXPECT_EQ(ReportTimes(out, "n1"), "30") << scope.keyword;
  EXPECT_EQ(ReportTimes(out, "n2"), "30") << scope.keyword;
}

void ExpectProcedureClocksOutsideDeclarations(const Scope& scope) {
  SimFixture f;
  std::string out = RunScope(
      scope,
      std::string(scope.procedure) + "  " + Failing("i1", "q1") + "  " +
          Covering("i2", "s1") + "  " + Failing("i3", "pcb.qp") + "  " +
          Covering("i4", "pcb.sp") + "  end\n",
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty()) << scope.keyword;
  EXPECT_EQ(ReportTimes(out, "i1"), "30") << scope.keyword;
  EXPECT_EQ(ReportTimes(out, "i2"), "30") << scope.keyword;
  EXPECT_EQ(ReportTimes(out, "i3"), "25") << scope.keyword;
  EXPECT_EQ(ReportTimes(out, "i4"), "25") << scope.keyword;
}

TEST(DefaultClockDeclarationRun, AModuleInstanceUnderAnExplicitClock) {
  ExpectExplicitClockSupersedes(kModule);
}

TEST(DefaultClockDeclarationRun, AModulesBlocksClockTheirDeclarations) {
  ExpectBlocksClockTheirDeclarations(kModule);
}

TEST(DefaultClockDeclarationRun, AModuleProcedureClocksOutsideDeclarations) {
  ExpectProcedureClocksOutsideDeclarations(kModule);
}

TEST(DefaultClockDeclarationRun, AnInterfaceInstanceUnderAnExplicitClock) {
  ExpectExplicitClockSupersedes(kInterface);
}

TEST(DefaultClockDeclarationRun, AnInterfacesBlocksClockTheirDeclarations) {
  ExpectBlocksClockTheirDeclarations(kInterface);
}

TEST(DefaultClockDeclarationRun,
     AnInterfaceProcedureClocksOutsideDeclarations) {
  ExpectProcedureClocksOutsideDeclarations(kInterface);
}

TEST(DefaultClockDeclarationRun, AProgramInstanceUnderAnExplicitClock) {
  ExpectExplicitClockSupersedes(kProgram);
}

TEST(DefaultClockDeclarationRun, AProgramsBlocksClockTheirDeclarations) {
  ExpectBlocksClockTheirDeclarations(kProgram);
}

TEST(DefaultClockDeclarationRun, ACheckerInstanceUnderAnExplicitClock) {
  ExpectExplicitClockSupersedes(kChecker);
}

TEST(DefaultClockDeclarationRun, ACheckersBlocksClockTheirDeclarations) {
  ExpectBlocksClockTheirDeclarations(kChecker);
}

TEST(DefaultClockDeclarationRun, ACheckerProcedureClocksOutsideDeclarations) {
  ExpectProcedureClocksOutsideDeclarations(kChecker);
}

constexpr const char* kFormalDeclarations =
    "  property q1(x, y); x |=> !y; endproperty\n"
    "  sequence s1(x, y); x ##1 y; endsequence\n";

constexpr const char* kFormalInstances =
    "  default clocking pcb @(posedge clk); endclocking\n"
    "  x1: assert property (@(negedge clk) q1(a, b))\n"
    "    else $display(\"x1 at %0d\", $time);\n"
    "  x2: cover property (@(negedge clk) s1(a, b))\n"
    "    $display(\"x2 at %0d\", $time);\n"
    "  always @(negedge clk) begin\n"
    "    i1: assert property (q1(a, b)) else $display(\"i1 at %0d\", $time);\n"
    "    i2: cover property (s1(a, b)) $display(\"i2 at %0d\", $time);\n"
    "  end\n";

void ExpectFormalInstancesOnTheNegedge(const std::string& design) {
  SimFixture f;
  std::string out = RunCapture(design, f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(ReportTimes(out, "x1"), "30");
  EXPECT_EQ(ReportTimes(out, "x2"), "30");
  EXPECT_EQ(ReportTimes(out, "i1"), "30");
  EXPECT_EQ(ReportTimes(out, "i2"), "30");
}

TEST(DefaultClockDeclarationRun, AnImportedPackageDeclaration) {
  ExpectFormalInstancesOnTheNegedge(
      ClockResolutionDesign(std::string("package p;\n") + kFormalDeclarations +
                            "endpackage\n"
                            "module m(input logic a, b, clk);\n"
                            "  import p::*;\n" +
                            kFormalInstances + "endmodule\n"));
}

TEST(DefaultClockDeclarationRun, DISABLED_ACompilationUnitDeclaration) {
  ExpectFormalInstancesOnTheNegedge(ClockResolutionDesign(
      std::string(kFormalDeclarations) + "module m(input logic a, b, clk);\n" +
      kFormalInstances + "endmodule\n"));
}

TEST(DefaultClockDeclarationRun, AGenerateBlockDeclaration) {
  ExpectFormalInstancesOnTheNegedge(ClockResolutionDesign(
      std::string("module m(input logic a, b, clk);\n"
                  "  if (1) begin : g\n") +
      kFormalDeclarations + kFormalInstances + "  end\nendmodule\n"));
}

TEST(DefaultClockDeclarationRun, AGenerateBlocksDefaultAndAModuleProperty) {
  SimFixture f;
  std::string out = RunCapture(
      ClockResolutionDesign("module m(input logic a, b, clk);\n"
                            "  property q1; a |=> !b; endproperty\n"
                            "  if (1) begin : g\n"
                            "    default clocking gc @(posedge clk);\n"
                            "    endclocking\n"
                            "    g1: assert property (@(negedge clk) q1)\n"
                            "      else $display(\"g1 at %0d\", $time);\n"
                            "    g2: assert property (q1)\n"
                            "      else $display(\"g2 at %0d\", $time);\n"
                            "  end\n"
                            "endmodule\n"),
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(ReportTimes(out, "g1"), "30");
  EXPECT_EQ(ReportTimes(out, "g2"), "25");
}

constexpr const char* kBlockHolders =
    "module sub(input logic x, y, ck);\n"
    "  clocking cb @(negedge ck);\n"
    "    property p; x |=> !y; endproperty\n"
    "    sequence s; x ##1 y; endsequence\n"
    "  endclocking\n"
    "endmodule\n"
    "interface ifc(input logic x, y, ck);\n"
    "  clocking cb @(negedge ck);\n"
    "    property p; x |=> !y; endproperty\n"
    "    sequence s; x ##1 y; endsequence\n"
    "  endclocking\n"
    "endinterface\n";

void ExpectPathInstancesOnTheBlocksClock(const std::string& default_decl) {
  SimFixture f;
  std::string out = RunCapture(
      ClockResolutionDesign(
          std::string(kBlockHolders) + "module m(input logic a, b, clk);\n" +
          default_decl +
          "  sub u(a, b, clk);\n"
          "  ifc i(a, b, clk);\n" +
          Failing("h1", "u.cb.p") + Covering("h2", "u.cb.s") +
          Failing("h3", "i.cb.p") + Covering("h4", "i.cb.s") + "endmodule\n"),
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty()) << default_decl;
  EXPECT_EQ(ReportTimes(out, "h1"), "30") << default_decl;
  EXPECT_EQ(ReportTimes(out, "h2"), "30") << default_decl;
  EXPECT_EQ(ReportTimes(out, "h3"), "30") << default_decl;
  EXPECT_EQ(ReportTimes(out, "h4"), "30") << default_decl;
}

TEST(ClockingBlockPathRun,
     DISABLED_AnotherInstancesBlockClocksItsDeclarations) {
  ExpectPathInstancesOnTheBlocksClock("");
}

TEST(ClockingBlockPathRun, DISABLED_AnotherInstancesBlockSupersedesTheDefault) {
  ExpectPathInstancesOnTheBlocksClock(
      "  default clocking dc @(posedge clk); endclocking\n");
}

TEST(ClockingBlockPathRun, ANonDefaultBlocksSequenceWithoutADefault) {
  SimFixture f;
  std::string out =
      RunCapture(ClockResolutionDesign("module m(input logic a, b, clk);\n"
                                       "  clocking cb @(negedge clk);\n"
                                       "    sequence s; a ##1 b; endsequence\n"
                                       "  endclocking\n" +
                                       Covering("c1", "cb.s") + "endmodule\n"),
                 f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(ReportTimes(out, "c1"), "30");
}

void ExpectInferredClockLeads(const Scope& scope, const std::string& open,
                              const std::string& close = "  end\n") {
  SimFixture f;
  std::string out = RunScope(
      scope,
      open + Failing("f1", "a |=> !b") + Failing("f2", "a |=> !b", "assume") +
          Covering("f3", "a ##1 b") +
          Covering("f4", "a ##1 b", "cover sequence") + close,
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty()) << scope.keyword << open;
  for (const char* label : {"f1", "f2", "f3", "f4"}) {
    EXPECT_EQ(ReportTimes(out, label), "30") << scope.keyword << open << label;
  }
}

TEST(InferredClockOverDefaultRun, EachStatementKindInAModuleAlways) {
  ExpectInferredClockLeads(kModule, kModule.procedure);
}

TEST(InferredClockOverDefaultRun, AnAlwaysFfOrAnInitialWithOneEventControl) {
  ExpectInferredClockLeads(kModule, "  always_ff @(negedge clk) begin\n");
  ExpectInferredClockLeads(kModule, "  initial forever @(negedge clk) begin\n");
}

TEST(InferredClockOverDefaultRun, AnAlwaysInAGenerateBlock) {
  ExpectInferredClockLeads(kModule,
                           "  if (1) begin : g\n"
                           "  always @(negedge clk) begin\n",
                           "  end\n  end\n");
}

TEST(InferredClockOverDefaultRun, AnInterfaceCheckerOrProgramProcedure) {
  ExpectInferredClockLeads(kInterface, kInterface.procedure);
  ExpectInferredClockLeads(kChecker, kChecker.procedure);
  ExpectInferredClockLeads(kProgram,
                           "  initial forever @(negedge clk) begin\n");
}

TEST(InferredClockOverDefaultRun, TheClausesA1AndA4) {
  SimFixture f;
  std::string out =
      RunScope(kModule,
               "  property q5; @(negedge clk) a |=> !b; endproperty\n" +
                   std::string(kModule.procedure) + "  " +
                   Failing("a1", "$rose(a) |=> !b") + "  " +
                   Failing("a4", "q5") + "  end\n",
               f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(ReportTimes(out, "a1"), "30");
  EXPECT_EQ(ReportTimes(out, "a4"), "30");
}

}  // namespace
