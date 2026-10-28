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

// A design elaborated with no top named, as the command line does, and what
// its run wrote to stdout.
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

// A module top around `items`, after the declarations `before`: clk rises at
// 5, 15, 25 and 35, a is low across the tick at 15 alone, and the run ends at
// 40, so an instance's assertion of a on clk's rise fails once, at 15, and
// reports the instance's level through %m.
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

// The checker every instance-placement case instantiates.
constexpr const char* kChecker =
    "checker chk(input logic clk, input logic a);\n"
    "  a1: assert property (@(posedge clk) a)\n"
    "    else $display(\"%m failed at %0d\", $time);\n"
    "endchecker\n";

// The lines of `out`, sorted, so that instances reporting in one time step
// are compared whatever order they report in.
std::vector<std::string> SortedLines(const std::string& out) {
  std::vector<std::string> lines;
  std::istringstream in(out);
  for (std::string line; std::getline(in, line);) lines.push_back(line);
  std::sort(lines.begin(), lines.end());
  return lines;
}

// §3.11 (printed page 55) with §23.3.1 and §24.3: a module or program
// instantiated nowhere is an implicit top-level instance, and one an interface
// instantiates (A.1.6 reaches program_instantiation from interface_item) is
// instantiated. p is instantiated in bus, so top alone roots the design; p was
// made a top too and its initial block ran twice.
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

// A program instantiated only in a module's generate block is instantiated, so
// t alone is a top and p runs once, as t.g.u; made a top too, it would print a
// second line under its own name.
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

// The same through an interface's generate block: top alone is a top, and p
// runs once beneath the interface instance, as top.b.g.u.
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

// Only modules and programs become implicit tops: a checker nothing
// instantiates is no top, and its assertion never runs, while top's own clock
// toggles beside it.
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

// Two programs nothing instantiates are two tops, each run once.
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

// §3.11: a module may instantiate checkers, in its generate blocks as in its
// body. Each instance of a generate loop is a level of its own, beneath its
// iteration's block, and each one's assertion is attempted.
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

// The same in a conditional generate block.
TEST(HierarchyInstances, CheckerInstanceInAModulesConditionalGenerateBlock) {
  EXPECT_EQ(RunUnderTop(kChecker,
                        "  if (1) begin : g\n"
                        "    chk c(clk, a);\n"
                        "  end\n"),
            "top.g.c.a1 failed at 15\n$finish at time 40\n");
}

// §3.11's example as written, top first: top holds mux2to1 m1, which holds its
// gates, so the design has two levels and top alone is a top. out1 follows in1
// while select is 0 and in2 once it is 1.
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

// §3.11: an interface may instantiate other building blocks. An interface
// instance in an interface's body and one in its generate block are each a
// level beneath the interface instance.
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

// A program instance in an interface's body runs once, a level beneath the
// interface instance.
TEST(HierarchyInstances, ProgramInstanceInAnInterfacesBody) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program p; initial $display(\"%m\"); endprogram\n"
                       "interface bus; p u(); endinterface\n"
                       "module top; bus b(); endmodule\n",
                       f),
            "top.b.u\n");
}

// A checker instance in an interface's body, its assertion attempted beneath
// the interface instance.
TEST(HierarchyInstances, CheckerInstanceInAnInterfacesBody) {
  EXPECT_EQ(RunUnderTop(std::string(kChecker) +
                            "interface bus(input logic clk, input logic a);\n"
                            "  chk c(clk, a);\n"
                            "endinterface\n",
                        "  bus b(clk, a);\n"),
            "top.b.c.a1 failed at 15\n$finish at time 40\n");
}

// The same in the interface's generate block.
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

// §3.11: a program may instantiate checkers, in its body and in its generate
// blocks, the checker declared ahead of the program here.
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

// The checker declared after the program that instantiates it.
TEST(HierarchyInstances, CheckerDeclaredAfterTheProgramInstantiatingIt) {
  EXPECT_EQ(RunUnderTop("program p(input logic clk, input logic a);\n"
                        "  chk c(clk, a);\n"
                        "endprogram\n" +
                            std::string(kChecker),
                        "  p u(clk, a);\n"),
            "top.u.c.a1 failed at 15\n$finish at time 40\n");
}

// A checker named through its package in a program.
TEST(HierarchyInstances, PackageScopedCheckerInstanceInAProgram) {
  EXPECT_EQ(RunUnderTop("package pkg;\n" + std::string(kChecker) +
                            "endpackage\n"
                            "program p(input logic clk, input logic a);\n"
                            "  pkg::chk c(clk, a);\n"
                            "endprogram\n",
                        "  p u(clk, a);\n"),
            "top.u.c.a1 failed at 15\n$finish at time 40\n");
}

// §3.11: a checker may instantiate checkers, in its generate blocks as in its
// body.
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
