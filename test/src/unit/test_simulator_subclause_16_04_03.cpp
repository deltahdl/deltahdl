#include <gtest/gtest.h>

#include <algorithm>
#include <sstream>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(StaticDeferredAssertionSim,
     ModuleLevelDeferredAssertExecutesWithoutProcedure) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a = 1'b0;\n"
      "  logic b = 1'b1;\n"
      "  int fires = 0;\n"
      "  function void count_fire; fires = fires + 1; endfunction\n"
      "  a1: assert #0 (a == b) else count_fire();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("fires");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StaticDeferredAssertionSim,
     ModuleLevelDeferredAssertReevaluatesOnOperandChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a = 1'b0;\n"
      "  logic b = 1'b0;\n"
      "  int fires = 0;\n"
      "  function void count_fire; fires = fires + 1; endfunction\n"
      "  a1: assert #0 (a == b) else count_fire();\n"
      "  initial #1 b = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("fires");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(StaticDeferredAssertionSim,
     ModuleLevelDeferredAssertIsFlushedByASecondOperandChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a = 4'd5;\n"
      "  logic [3:0] b = 4'd5;\n"
      "  int fires = 0;\n"
      "  function void count_fire; fires = fires + 1; endfunction\n"
      "  a1: assert #0 (a == b) else count_fire();\n"
      "  initial begin\n"
      "    #1 a = 4'd7;\n"
      "    #0 b = 4'd7;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("fires");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(StaticDeferredAssertionSim, ModuleLevelDeferredAssertNamesItsLabel) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a = 1'b0;\n"
      "  logic b = 1'b1;\n"
      "  a1: assert #0 (a == b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityScope(), "m.a1");
  EXPECT_EQ(f.ctx.LastSeverityLine(), 4u);
}

const char kStimulus[] =
    "  initial begin #10 a = 1; #10 b = 1; #10 a = 0; #0 b = 0; end\n";
const char kAction[] = " $display(\"%0t %m\", $time);\n";

std::string SortedLines(const std::string& out) {
  std::vector<std::string> lines;
  std::istringstream in(out);
  for (std::string line; std::getline(in, line);) lines.push_back(line);
  std::sort(lines.begin(), lines.end());
  std::string joined;
  for (const auto& line : lines) joined += line + "\n";
  return joined;
}

std::string RunSorted(const std::string& src) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  return SortedLines(out);
}

std::string TopWith(const std::string& items, const std::string& outside = "") {
  return outside + "module t;\n  logic a = 0, b = 0;\n" + items + kStimulus +
         "endmodule\n";
}

TEST(StaticDeferredAssertionSim, StaticAssumeFormsRunAsAlwaysComb) {
  for (const char* form : {"assume #0", "assume final"}) {
    EXPECT_EQ(RunSorted(TopWith(std::string("  m1: ") + form +
                                " (a == b) else" + kAction)),
              "10 t.m1\n")
        << form;
  }
}

TEST(StaticDeferredAssertionSim, AStaticCoverFinalCountsOnlyUnflushedRuns) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(TopWith(std::string("  m3: cover final (a != b)") + kAction),
                 f),
      "10 t.m3\n");
  const auto& results = f.ctx.ImmediateCovers().Results();
  ASSERT_EQ(results.size(), 1u);
  EXPECT_EQ(results[0].evaluated, 4u);
  EXPECT_EQ(results[0].succeeded, 1u);
}

TEST(StaticDeferredAssertionSim, AnInterfacesStaticAssertionsRunAsAlwaysComb) {
  EXPECT_EQ(RunSorted(TopWith("  ifc u(a, b);\n",
                              std::string("interface ifc(input logic a, b);\n"
                                          "  ia: assert #0 (a == b) else") +
                                  kAction + "  fa: assert final (a == b) else" +
                                  kAction + "endinterface\n")),
            "10 t.u.fa\n10 t.u.ia\n");
}

const char kGenerated[] =
    "  if (1) begin : g\n"
    "    ga: assert #0 (a == b) else $display(\"%0t %m\", $time);\n"
    "  end\n"
    "  for (genvar i = 0; i < 2; i++) begin : gl\n"
    "    la: assert final (a == b) else $display(\"%0t %m\", $time);\n"
    "  end\n"
    "  case (2)\n"
    "    1: begin : x\n"
    "      xa: assert #0 (a == b) else $display(\"%0t %m\", $time);\n"
    "    end\n"
    "    2: begin : y\n"
    "      ya: assert #0 (a == b) else $display(\"%0t %m\", $time);\n"
    "    end\n"
    "  endcase\n";

TEST(StaticDeferredAssertionSim, AModulesGenerateBlocksRunTheirAssertions) {
  EXPECT_EQ(RunSorted(TopWith(kGenerated)),
            "10 t.g.ga\n10 t.gl[0].la\n10 t.gl[1].la\n10 t.y.ya\n");
}

TEST(StaticDeferredAssertionSim, AnInterfacesGenerateBlocksRunTheirAssertions) {
  EXPECT_EQ(
      RunSorted(TopWith("  ifc u(a, b);\n",
                        std::string("interface ifc(input logic a, b);\n") +
                            kGenerated + "endinterface\n")),
      "10 t.u.g.ga\n10 t.u.gl[0].la\n10 t.u.gl[1].la\n10 t.u.y.ya\n");
}

}  // namespace
