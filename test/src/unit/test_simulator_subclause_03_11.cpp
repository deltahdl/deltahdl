#include <gtest/gtest.h>

#include <algorithm>
#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

struct AllTopsRun {
  RtlirDesign* design;
  std::string out;
};

AllTopsRun RunAllTops(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrcAllTops(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return {design, captured.str()};
}

std::string RunUnderTop(const std::string& before, const std::string& items) {
  SimFixture f;
  return RunCapture(before +
                        "module top;\n"
                        "  logic clk = 0;\n"
                        "  logic a = 1;\n"
                        "  always #5 clk = ~clk;\n" +
                        items +
                        "  initial begin\n"
                        "    #10 a = 0;\n"
                        "    #10 a = 1;\n"
                        "    #20 $finish;\n"
                        "  end\n"
                        "endmodule\n",
                    f);
}

constexpr const char* kChecker =
    "checker chk(input logic clk, input logic a);\n"
    "  a1: assert property (@(posedge clk) a)\n"
    "    else $display(\"%m failed at %0d\", $time);\n"
    "endchecker\n";

std::vector<std::string> SortedLines(const std::string& out) {
  std::vector<std::string> lines;
  std::istringstream in(out);
  for (std::string line; std::getline(in, line);) lines.push_back(line);
  std::sort(lines.begin(), lines.end());
  return lines;
}

TEST(ImplicitTopLevelInstances, ProgramInstantiatedInAnInterfaceIsNoTop) {
  SimFixture f;
  auto* design = ElaborateSrcAllTops(
      "program p; initial $display(\"%m\"); endprogram\n"
      "interface bus; p u(); endinterface\n"
      "module top; bus b(); endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

TEST(ImplicitTopLevelInstances, ProgramInAModulesGenerateBlockIsNoTop) {
  SimFixture f;
  auto run = RunAllTops(
      "program p; initial $display(\"%m\"); endprogram\n"
      "module t;\n"
      "  if (1) begin : g\n"
      "    p u();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(run.design, nullptr);
  ASSERT_EQ(run.design->top_modules.size(), 1u);
  EXPECT_EQ(run.design->top_modules[0]->name, "t");
  EXPECT_EQ(run.out, "t.g.u\n");
}

TEST(ImplicitTopLevelInstances, ProgramInAnInterfacesGenerateBlockIsNoTop) {
  SimFixture f;
  auto run = RunAllTops(
      "program p; initial $display(\"%m\"); endprogram\n"
      "interface bus;\n"
      "  if (1) begin : g\n"
      "    p u();\n"
      "  end\n"
      "endinterface\n"
      "module top; bus b(); endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(run.design, nullptr);
  ASSERT_EQ(run.design->top_modules.size(), 1u);
  EXPECT_EQ(run.design->top_modules[0]->name, "top");
  EXPECT_EQ(run.out, "top.b.g.u\n");
}

TEST(ImplicitTopLevelInstances, UninstantiatedCheckerIsNoTopAndNeverRuns) {
  SimFixture f;
  auto run = RunAllTops(
      "checker lone(logic clk);\n"
      "  a1: assert property (@(posedge clk) 0) else $display(\"fail\");\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  initial repeat (4) #5 clk = ~clk;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(run.design, nullptr);
  ASSERT_EQ(run.design->top_modules.size(), 1u);
  EXPECT_EQ(run.design->top_modules[0]->name, "top");
  EXPECT_EQ(run.out, "");
}

TEST(ImplicitTopLevelInstances, TwoUninstantiatedProgramsAreTwoTops) {
  SimFixture f;
  auto run = RunAllTops(
      "program p1; initial $display(\"p1\"); endprogram\n"
      "program p2; initial $display(\"p2\"); endprogram\n",
      f);
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(run.design, nullptr);
  ASSERT_EQ(run.design->top_modules.size(), 2u);
  EXPECT_EQ(run.design->top_modules[0]->name, "p1");
  EXPECT_EQ(run.design->top_modules[1]->name, "p2");
  EXPECT_TRUE(run.out == "p1\np2\n" || run.out == "p2\np1\n") << run.out;
}

TEST(HierarchyInstances, CheckerInstancesInAModulesGenerateLoop) {
  EXPECT_EQ(SortedLines(RunUnderTop(kChecker,
                                    "  for (genvar i = 0; i < 3; i++) "
                                    "begin : g\n"
                                    "    chk c(clk, a);\n"
                                    "  end\n")),
            (std::vector<std::string>{
                "$finish at time 40", "top.g[0].c.a1 failed at 15",
                "top.g[1].c.a1 failed at 15", "top.g[2].c.a1 failed at 15"}));
}

TEST(HierarchyInstances, CheckerInstanceInAModulesConditionalGenerateBlock) {
  EXPECT_EQ(RunUnderTop(kChecker,
                        "  if (1) begin : g\n"
                        "    chk c(clk, a);\n"
                        "  end\n"),
            "top.g.c.a1 failed at 15\n$finish at time 40\n");
}

TEST(HierarchyInstances, TheMux2to1ExampleIsTwoLevels) {
  SimFixture f;
  auto run = RunAllTops(
      "module top;\n"
      "  logic in1, in2, select;\n"
      "  wire out1;\n"
      "  mux2to1 m1 (.a(in1), .b(in2), .sel(select), .y(out1));\n"
      "  logic r0, r1;\n"
      "  initial begin\n"
      "    in1 = 1; in2 = 0; select = 0;\n"
      "    #1 r0 = out1;\n"
      "    select = 1;\n"
      "    #1 r1 = out1;\n"
      "  end\n"
      "endmodule: top\n"
      "module mux2to1 (input wire a, b, sel,\n"
      "                output logic y);\n"
      "  not g1 (sel_n, sel);\n"
      "  and g2 (a_s, a, sel_n);\n"
      "  and g3 (b_s, b, sel);\n"
      "  or  g4 (y, a_s, b_s);\n"
      "endmodule: mux2to1\n",
      f);
  EXPECT_FALSE(f.has_errors);
  ASSERT_NE(run.design, nullptr);
  ASSERT_EQ(run.design->top_modules.size(), 1u);
  const auto* top = run.design->top_modules[0];
  EXPECT_EQ(top->name, "top");
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].inst_name, "m1");
  ASSERT_NE(top->children[0].resolved, nullptr);
  EXPECT_EQ(top->children[0].resolved->name, "mux2to1");
  auto* r0 = f.ctx.FindVariable("r0");
  auto* r1 = f.ctx.FindVariable("r1");
  ASSERT_NE(r0, nullptr);
  ASSERT_NE(r1, nullptr);
  EXPECT_EQ(r0->value.ToUint64(), 1u);
  EXPECT_EQ(r1->value.ToUint64(), 0u);
}

TEST(HierarchyInstances, InterfaceInstancesInAnInterfacesBodyAndGenerateBlock) {
  SimFixture f;
  EXPECT_EQ(SortedLines(RunCapture("interface leaf;\n"
                                   "  initial $display(\"%m\");\n"
                                   "endinterface\n"
                                   "interface bus;\n"
                                   "  leaf l0();\n"
                                   "  if (1) begin : g\n"
                                   "    leaf l1();\n"
                                   "  end\n"
                                   "endinterface\n"
                                   "module top; bus b(); endmodule\n",
                                   f)),
            (std::vector<std::string>{"top.b.g.l1", "top.b.l0"}));
}

TEST(HierarchyInstances, ProgramInstanceInAnInterfacesBody) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program p; initial $display(\"%m\"); endprogram\n"
                       "interface bus; p u(); endinterface\n"
                       "module top; bus b(); endmodule\n",
                       f),
            "top.b.u\n");
}

TEST(HierarchyInstances, CheckerInstanceInAnInterfacesBody) {
  EXPECT_EQ(RunUnderTop(std::string(kChecker) +
                            "interface bus(input logic clk, input logic a);\n"
                            "  chk c(clk, a);\n"
                            "endinterface\n",
                        "  bus b(clk, a);\n"),
            "top.b.c.a1 failed at 15\n$finish at time 40\n");
}

TEST(HierarchyInstances, CheckerInstanceInAnInterfacesGenerateBlock) {
  EXPECT_EQ(RunUnderTop(std::string(kChecker) +
                            "interface bus(input logic clk, input logic a);\n"
                            "  if (1) begin : g\n"
                            "    chk c(clk, a);\n"
                            "  end\n"
                            "endinterface\n",
                        "  bus b(clk, a);\n"),
            "top.b.g.c.a1 failed at 15\n$finish at time 40\n");
}

TEST(HierarchyInstances, CheckerInstanceInAProgramsBody) {
  EXPECT_EQ(RunUnderTop(std::string(kChecker) +
                            "program p(input logic clk, input logic a);\n"
                            "  chk c(clk, a);\n"
                            "endprogram\n",
                        "  p u(clk, a);\n"),
            "top.u.c.a1 failed at 15\n$finish at time 40\n");
}

TEST(HierarchyInstances, CheckerInstanceInAProgramsGenerateBlock) {
  EXPECT_EQ(RunUnderTop(std::string(kChecker) +
                            "program p(input logic clk, input logic a);\n"
                            "  if (1) begin : g\n"
                            "    chk c(clk, a);\n"
                            "  end\n"
                            "endprogram\n",
                        "  p u(clk, a);\n"),
            "top.u.g.c.a1 failed at 15\n$finish at time 40\n");
}

TEST(HierarchyInstances, CheckerDeclaredAfterTheProgramInstantiatingIt) {
  EXPECT_EQ(RunUnderTop("program p(input logic clk, input logic a);\n"
                        "  chk c(clk, a);\n"
                        "endprogram\n" +
                            std::string(kChecker),
                        "  p u(clk, a);\n"),
            "top.u.c.a1 failed at 15\n$finish at time 40\n");
}

TEST(HierarchyInstances, PackageScopedCheckerInstanceInAProgram) {
  EXPECT_EQ(RunUnderTop("package pkg;\n" + std::string(kChecker) +
                            "endpackage\n"
                            "program p(input logic clk, input logic a);\n"
                            "  pkg::chk c(clk, a);\n"
                            "endprogram\n",
                        "  p u(clk, a);\n"),
            "top.u.c.a1 failed at 15\n$finish at time 40\n");
}

TEST(HierarchyInstances, CheckerInstanceInACheckersGenerateBlock) {
  EXPECT_EQ(RunUnderTop(std::string(kChecker) +
                            "checker outer(input logic clk, input logic a);\n"
                            "  if (1) begin : g\n"
                            "    chk i1(clk, a);\n"
                            "  end\n"
                            "endchecker\n",
                        "  outer o(clk, a);\n"),
            "top.o.g.i1.a1 failed at 15\n$finish at time 40\n");
}

}  // namespace
