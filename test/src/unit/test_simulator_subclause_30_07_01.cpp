#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "elaborator/elaborator.h"
#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "lexer/lexer.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/parser.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

PathDelay MakePathWithDelays(uint64_t value) {
  PathDelay pd;
  pd.delay_count = 1;
  for (int i = 0; i < 12; ++i) pd.delays[i] = value;
  InitDefaultPulseLimits(pd);
  return pd;
}

TEST(ApplyPulseControlOverride, PreservesPropagationDelays) {
  PathDelay pd = MakePathWithDelays(10);
  ApplyPulseControlOverride(pd, 4, true, 8);
  for (int i = 0; i < 12; ++i) EXPECT_EQ(pd.delays[i], 10u);
}

void BuildResolvedSpecify(const std::string& specify_body, SimFixture& f,
                          SpecifyManager& mgr,
                          const std::string& module_items = "") {
  std::string code = "module t(input clk, input data, input pre, output q);\n" +
                     module_items + "  specify\n" + specify_body +
                     "\n  endspecify\nendmodule\n";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  LowerAndRun(design, f);

  for (auto* item : cu->modules.back()->items) {
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (auto* si : item->specify_items) {
      if (si->kind == SpecifyItemKind::kPathDecl) {
        PathDelay pd = BuildPathDelayFromDecl(si->path, f.ctx, f.arena);
        InitDefaultPulseLimits(pd);
        mgr.AddPathDelay(pd);
      }
    }
  }
  RegisterPathPulseSpecparams(*cu->modules.back(), f, mgr);
}

const PathDelay* FindPath(const SpecifyManager& mgr, std::string_view src,
                          std::string_view dst) {
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == src && pd.dst_port == dst) return &pd;
  }
  return nullptr;
}

TEST(PulseControlResolution, RejectOnlyMirrorsErrorFromSource) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk => q) = 12;\n"
      "    specparam PATHPULSE$ = (4);",
      f, mgr);
  const PathDelay* p = FindPath(mgr, "clk", "q");
  ASSERT_NE(p, nullptr);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(p->reject_limit[i], 4u);
    EXPECT_EQ(p->error_limit[i], 4u);
  }
}

TEST(PulseControlResolution, NonPathSpecificAppliesToEveryPath) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk => q) = 12;\n"
      "    (data => q) = 10;\n"
      "    specparam PATHPULSE$ = (3, 7);",
      f, mgr);
  const PathDelay* a = FindPath(mgr, "clk", "q");
  const PathDelay* b = FindPath(mgr, "data", "q");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(a->reject_limit[i], 3u);
    EXPECT_EQ(a->error_limit[i], 7u);
    EXPECT_EQ(b->reject_limit[i], 3u);
    EXPECT_EQ(b->error_limit[i], 7u);
  }
}

TEST(PulseControlResolution, PathSpecificWinsRegardlessOfOrder) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk => q) = 12;\n"
      "    (data => q) = 10;\n"
      "    specparam PATHPULSE$clk$q = (2, 9);\n"
      "    specparam PATHPULSE$ = (3);",
      f, mgr);
  const PathDelay* named = FindPath(mgr, "clk", "q");
  const PathDelay* other = FindPath(mgr, "data", "q");
  ASSERT_NE(named, nullptr);
  ASSERT_NE(other, nullptr);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(named->reject_limit[i], 2u);
    EXPECT_EQ(named->error_limit[i], 9u);
    EXPECT_EQ(other->reject_limit[i], 3u);
    EXPECT_EQ(other->error_limit[i], 3u);
  }
}

TEST(PulseControlResolution, LimitValueFromSpecparamConstant) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    specparam lim = 5;\n"
      "    (clk => q) = 12;\n"
      "    specparam PATHPULSE$ = (lim);",
      f, mgr);
  const PathDelay* p = FindPath(mgr, "clk", "q");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->reject_limit[0], 5u);
  EXPECT_EQ(p->error_limit[0], 5u);
}

TEST(PulseControlResolution, MultiPathFirstTerminalAppliesNonFirstIgnored) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk, pre *> q) = 4;\n"
      "    specparam PATHPULSE$clk$q = (1, 2);\n"
      "    specparam PATHPULSE$pre$q = (9);",
      f, mgr);
  const PathDelay* p = FindPath(mgr, "clk", "q");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->reject_limit[0], 1u);
  EXPECT_EQ(p->error_limit[0], 2u);
}

TEST(PulseControlResolution, LimitValueFromParameterConstant) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk => q) = 12;\n"
      "    specparam PATHPULSE$ = (P);",
      f, mgr, "  parameter P = 6;\n");
  const PathDelay* p = FindPath(mgr, "clk", "q");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->reject_limit[0], 6u);
  EXPECT_EQ(p->error_limit[0], 6u);
}

TEST(PulseControlResolution, LimitValueFromLocalparamConstant) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk => q) = 12;\n"
      "    specparam PATHPULSE$ = (L);",
      f, mgr, "  localparam L = 7;\n");
  const PathDelay* p = FindPath(mgr, "clk", "q");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->reject_limit[0], 7u);
  EXPECT_EQ(p->error_limit[0], 7u);
}

TEST(PulseControlResolution, LimitValueMintypmaxSelectsTypical) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk => q) = 12;\n"
      "    specparam PATHPULSE$ = (2:5:9);",
      f, mgr);
  const PathDelay* p = FindPath(mgr, "clk", "q");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->reject_limit[0], 5u);
  EXPECT_EQ(p->error_limit[0], 5u);
}

TEST(PulseControlResolution, PathSpecificAffectsOnlyNamedPath) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk => q) = 12;\n"
      "    (data => q) = 8;\n"
      "    specparam PATHPULSE$clk$q = (2, 5);",
      f, mgr);
  const PathDelay* named = FindPath(mgr, "clk", "q");
  const PathDelay* other = FindPath(mgr, "data", "q");
  ASSERT_NE(named, nullptr);
  ASSERT_NE(other, nullptr);
  EXPECT_EQ(named->reject_limit[0], 2u);
  EXPECT_EQ(named->error_limit[0], 5u);
  EXPECT_EQ(other->reject_limit[0], 8u);
  EXPECT_EQ(other->error_limit[0], 8u);
}

TEST(PulseControlResolution, UnmatchedPathSpecificIsIgnored) {
  SimFixture f;
  SpecifyManager mgr;
  BuildResolvedSpecify(
      "    (clk => q) = 12;\n"
      "    specparam PATHPULSE$data$q = (2, 4);",
      f, mgr);
  const PathDelay* p = FindPath(mgr, "clk", "q");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->reject_limit[0], 12u);
  EXPECT_EQ(p->error_limit[0], 12u);
}

TEST(PulseControlResolution, StandardExampleNonspecificLimitReachesPath) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t(input clk, input data, input clr, input pre, output q);\n"
      "  specify\n"
      "    (clk => q) = 12;\n"
      "    (data => q) = 10;\n"
      "    (clr, pre *> q) = 4;\n"
      "\n"
      "  specparam\n"
      "      PATHPULSE$clk$q = (2,9),\n"
      "      PATHPULSE$clr$q = (0,4),\n"
      "      PATHPULSE$ = (3);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  SpecifyManager* installed = f.ctx.GetSpecifyManager();
  ASSERT_NE(installed, nullptr);
  const PathDelay* unnamed = FindPath(*installed, "data", "q");
  ASSERT_NE(unnamed, nullptr);
  EXPECT_EQ(unnamed->reject_limit[0], 3u);
  EXPECT_EQ(unnamed->error_limit[0], 3u);
}

std::string BufferPulseDesign(const std::string& specify_body) {
  return "module mybuf(input a, output y);\n"
         "  assign y = a;\n"
         "  specify\n" +
         specify_body +
         "  endspecify\n"
         "endmodule\n"
         "module top;\n"
         "  logic a;\n"
         "  wire ty;\n"
         "  mybuf u(.a(a), .y(ty));\n"
         "  always @(ty) if ($time > 0) $display(\"t=%0t y=%b\", $time, ty);\n"
         "  initial begin\n"
         "    a = 1;\n"
         "    #10 a = 0;\n"
         "    #4 a = 1;\n"
         "  end\n"
         "endmodule\n";
}

TEST(PulseControlRun, NonspecificLimitReachesEveryPath) {
  SimFixture f;
  EXPECT_EQ(RunCapture(BufferPulseDesign("    (a => y) = 7;\n"
                                         "    specparam PATHPULSE$ = (3);\n"),
                       f),
            "t=7 y=1\nt=17 y=0\nt=21 y=1\n");
}

TEST(PulseControlRun, ZeroLimitsLetEveryPulsePropagate) {
  SimFixture f;
  EXPECT_EQ(RunCapture(BufferPulseDesign("    specparam PATHPULSE$ = (0);\n"
                                         "    (a => y) = (7, 9);\n"),
                       f),
            "t=7 y=1\nt=19 y=0\nt=21 y=1\n");
}

TEST(PulseControlRun, PulseBetweenTheLimitsIsFilteredToX) {
  SimFixture f;
  EXPECT_EQ(RunCapture(BufferPulseDesign("    specparam PATHPULSE$ = (1, 5);\n"
                                         "    (a => y) = (7, 9);\n"),
                       f),
            "t=7 y=1\nt=19 y=x\nt=21 y=1\n");
}

TEST(PulseControlRun, PathSpecificLimitsTakePrecedence) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module myand(input a, input b, output y);\n"
                       "  assign y = a & b;\n"
                       "  specify\n"
                       "    specparam PATHPULSE$a$y = (0, 0);\n"
                       "    specparam PATHPULSE$ = (3);\n"
                       "    (a => y) = (7, 9);\n"
                       "    (b => y) = (7, 9);\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic a, b;\n"
                       "  wire ty;\n"
                       "  myand u(.a(a), .b(b), .y(ty));\n"
                       "  always @(ty) if ($time > 0)\n"
                       "    $display(\"t=%0t y=%b\", $time, ty);\n"
                       "  initial begin\n"
                       "    a = 1; b = 1;\n"
                       "    #10 a = 0;\n"
                       "    #4 a = 1;\n"
                       "    #26 b = 0;\n"
                       "    #4 b = 1;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=7 y=1\nt=19 y=0\nt=21 y=1\n");
}

TEST(PulseControlRun, MultiplePathStatementTakesItsFirstTerminalsLimits) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module mycell(input clr, input pre, output q);\n"
                       "  assign q = clr & pre;\n"
                       "  specify\n"
                       "    (clr, pre *> q) = 4;\n"
                       "    specparam PATHPULSE$clr$q = (0, 4);\n"
                       "  endspecify\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic clr, pre;\n"
                       "  wire tq;\n"
                       "  mycell u(.clr(clr), .pre(pre), .q(tq));\n"
                       "  always @(tq) if ($time > 0)\n"
                       "    $display(\"t=%0t q=%b\", $time, tq);\n"
                       "  initial begin\n"
                       "    clr = 1; pre = 1;\n"
                       "    #10 pre = 0;\n"
                       "    #2 pre = 1;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=4 q=1\nt=14 q=x\nt=16 q=1\n");
}

}  // namespace
