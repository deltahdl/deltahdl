#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(HierarchicalNameSimulation, ReadChildInstanceVariable) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module child;\n"
      "  logic [7:0] val;\n"
      "  initial val = 8'd42;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    #1;\n"
      "    result = c1.val;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
}

TEST(HierarchicalNameSimulation, WriteChildInstanceVariable) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module child;\n"
      "  logic [7:0] val;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  initial begin\n"
      "    c1.val = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "c1.val");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 99u);
}

TEST(HierarchicalNameSimulation, MultiLevelHierarchicalRead) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module leaf;\n"
      "  logic [7:0] data;\n"
      "  initial data = 8'd77;\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l1();\n"
      "endmodule\n"
      "module top;\n"
      "  mid m1();\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    #1;\n"
      "    result = m1.l1.data;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 77u);
}

TEST(HierarchicalNameSimulation, RootPrefixedHierarchicalRead) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] sig;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    sig = 8'd33;\n"
      "    #1;\n"
      "    result = $root.top.sig;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 33u);
}

TEST(HierarchicalNameSimulation, HierarchicalNameInEventExpression) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module child;\n"
      "  logic done;\n"
      "  initial begin\n"
      "    done = 0;\n"
      "    #10 done = 1;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result = 8'd0;\n"
      "    @(posedge c1.done);\n"
      "    result = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 1u);
}

TEST(HierarchicalNames, InstanceArrayElementIsReachedByItsIndex) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf #(parameter K = 0)();\n"
                       "  int v = K * 10 + 1;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  leaf #(1) arr[2]();\n"
                       "  leaf #(5) one();\n"
                       "  initial begin\n"
                       "    arr[1].v = 11;\n"
                       "    #1 $display(\"%0d %0d %0d\", arr[1].v, arr[0].v, "
                       "one.v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "11 11 51\n");
}

TEST(HierarchicalNames, RangedInstanceArrayElementIsReachedByItsIndex) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf(input i, output o);\n"
                       "  assign o = ~i;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  reg [1:0] a = 2'b01; wire [1:0] y;\n"
                       "  leaf arr[1:0](.i(a), .o(y));\n"
                       "  initial #1 $display(\"%b %b %b\", y, arr[1].o, "
                       "arr[0].o);\n"
                       "endmodule\n",
                       f),
            "10 1 0\n");
}

TEST(HierarchicalNames, ReadOfAnUnsignedVariableByHierarchicalNameIsUnsigned) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("interface I; logic w; endinterface\n"
                 "module sub;\n"
                 "  logic u;\n"
                 "  logic signed [3:0] s;\n"
                 "  int i;\n"
                 "endmodule\n"
                 "module top;\n"
                 "  I a();\n"
                 "  sub b();\n"
                 "  initial begin\n"
                 "    a.w = 1; b.u = 1; b.s = -3; b.i = -5;\n"
                 "    #1 $display(\"%0d %0d %0d %0d\", a.w, b.u, b.s, b.i);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "1 1 -3 -5\n");
}

TEST(HierarchicalNames, RootHeadedArrayElementIsTheTopsElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub;\n"
                       "  logic arr [1:0] = '{1, 1};\n"
                       "  initial begin\n"
                       "    arr[1] = 0;\n"
                       "    $root.top.arr[0] = 0;\n"
                       "    #1 $display(\"%0d %0d %0d\", $root.top.arr[1],\n"
                       "                $root.top.arr[0], arr[0]);\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic arr [1:0] = '{1, 1};\n"
                       "  sub c();\n"
                       "endmodule\n",
                       f),
            "1 0 1\n");
}

TEST(HierarchicalNames, MemberOfAnotherInstancesStructureIsWritten) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int A; int B; } s_t;\n"
                       "module sub ();\n"
                       "  s_t v = '{A: 1, B: 2};\n"
                       "  initial #2 $display(\"A=%0d B=%0d\", v.A, v.B);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  sub s1 ();\n"
                       "  initial begin\n"
                       "    #1 s1.v.B = 9;\n"
                       "    s1.v.A <= 4;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "A=4 B=9\n");
}

TEST(HierarchicalNames, MemberOfATypeParameterStructureIsWritten) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int A; } a_t;\n"
                       "module ma #(parameter type t_3 = int) ();\n"
                       "  t_3 v3;\n"
                       "  initial #2 $display(\"A=%0d\", v3.A);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  ma #(.t_3(a_t)) s2 ();\n"
                       "  initial #1 s2.v3.A = 9;\n"
                       "endmodule\n",
                       f),
            "A=9\n");
}

TEST(HierarchicalNames, NameThroughAGenerateBlockReachesAnInstancesVariable) {
  SimFixture f;
  std::string out = RunCapture(
      "module m2;\n"
      "  int n = 3;\n"
      "  int dbl;\n"
      "  always @(n) dbl = n * 2;\n"
      "endmodule\n"
      "module top;\n"
      "  if (1) begin : g\n"
      "    m2 c();\n"
      "  end\n"
      "  for (genvar i = 0; i < 2; i++) begin : h\n"
      "    m2 d();\n"
      "  end\n"
      "  initial begin\n"
      "    #1 h[1].d.n = 7;\n"
      "    #1 $display(\"%0d %0d %0d %0d\", g.c.n, h[0].d.n, h[1].d.n,\n"
      "                h[1].d.dbl);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 3 7 14\n");
}

TEST(HierarchicalNameTree, OneNamedBlockInTwoInstancesIsTwoObjects) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module mod(input in);\n"
                       "  always @(posedge in) begin : keep\n"
                       "    logic hold;\n    hold = in;\n  end\n"
                       "endmodule\n"
                       "module cct(input s1, s2);\n"
                       "  mod amod(s1), bmod(s2);\nendmodule\n"
                       "module wave;\n  logic s1 = 0, s2 = 0;\n"
                       "  cct a(s1, s2);\n"
                       "  initial begin\n    #1 s1 = 1;\n"
                       "    #1 $display(\"%b %b\", a.amod.keep.hold, "
                       "a.bmod.keep.hold);\n  end\nendmodule\n",
                       f),
            "1 x\n");
}

std::string OutputActualRun(const std::string& routine, SimFixture& f) {
  return RunCapture(
      "module leaf;\n  logic [3:0] v;\nendmodule\n"
      "module t;\n  leaf u();\n" +
          routine +
          "  initial begin\n    put(u.v);\n"
          "    #1 $display(\"%0d\", u.v);\n  end\nendmodule\n",
      f);
}

TEST(HierarchicalNameTree, AHierarchicalNameIsATasksOutputActual) {
  SimFixture f;
  EXPECT_EQ(OutputActualRun("  task put(output logic [3:0] o);\n"
                            "    o = 4'd9;\n  endtask\n",
                            f),
            "9\n");
}

TEST(HierarchicalNameTree, AHierarchicalNameIsAFunctionsOutputActual) {
  SimFixture f;
  EXPECT_EQ(OutputActualRun("  function void put(output logic [3:0] o);\n"
                            "    o = 4'd9;\n  endfunction\n",
                            f),
            "9\n");
}

TEST(HierarchicalNameTree, AnEscapedInstanceNameHeadsAPath) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf;\n  int v = 7;\nendmodule\n"
                       "module t;\n  leaf \\in-st ();\n"
                       "  initial #1 $display(\"%0d\", \\in-st .v);\n"
                       "endmodule\n",
                       f),
            "7\n");
}

TEST(HierarchicalNameTree, AnEscapedNameEndsAPath) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf;\n  int \\v-1  = 8;\nendmodule\n"
                       "module t;\n  leaf u();\n"
                       "  initial #1 $display(\"%0d\", u.\\v-1 );\n"
                       "endmodule\n",
                       f),
            "8\n");
}

TEST(HierarchicalNameTree, StaticLocalsAreReachedThroughTheirSubroutine) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf;\n"
                       "  task tk;\n    static int n = 0;\n    n++;\n"
                       "  endtask\n"
                       "  function int fn;\n    static int k = 0;\n"
                       "    k++;\n    return k;\n  endfunction\n"
                       "endmodule\n"
                       "module t;\n  leaf u();\n  int r;\n"
                       "  initial begin\n    u.tk();\n    u.tk();\n"
                       "    r = u.fn();\n"
                       "    #1 $display(\"%0d %0d\", u.tk.n, u.fn.k);\n"
                       "  end\nendmodule\n",
                       f),
            "2 1\n");
}

TEST(HierarchicalNameTree, ALaterForkWritesAnEarlierForksVariable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n  initial begin\n"
                       "    fork : mod_1\n      reg x;\n"
                       "      #2 $display(\"%b\", x);\n    join_none\n"
                       "    fork : mod_2\n      reg x;\n"
                       "      #1 mod_1.x = 1;\n    join_none\n"
                       "  end\nendmodule\n",
                       f),
            "1\n");
}

TEST(HierarchicalNameTree, AnElementOfATwoDimensionalInstanceArray) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf;\n  int v;\nendmodule\n"
                       "module t;\n  leaf u [0:3][0:3] ();\n"
                       "  initial begin\n    u[1][2].v = 6;\n"
                       "    #1 $display(\"%0d %0d\", u[1][2].v, u[2][1].v);\n"
                       "  end\nendmodule\n",
                       f),
            "6 0\n");
}

TEST(HierarchicalNameTree, APathMayEndAtAnArrayOrLoopBlockName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf;\nendmodule\n"
                       "module t;\n  leaf u [0:3] ();\n"
                       "  for (genvar i = 0; i < 4; i++) begin : blk\n"
                       "    int w = i;\n  end\n"
                       "  initial begin\n    $printtimescale(u);\n"
                       "    $printtimescale(t.blk);\n  end\nendmodule\n",
                       f),
            "Time scale of (u) is 1ns / 1ns\n"
            "Time scale of (t.blk) is 1ns / 1ns\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

std::string LabelScopeRun(const std::string& body, const std::string& top_items,
                          SimFixture& f) {
  return RunCaptureAllTops(
      "module top();\n  logic clk = 0, x = 1, y = 0, z = 1;\n"
      "  initial repeat (6) #5 clk = ~clk;\n"
      "  m m_i(clk, x, y, z);\n" +
          top_items +
          "endmodule\n"
          "module m(input logic clk, a, b, c);\n" +
          body + "endmodule\n",
      f);
}

bool Has(const std::string& out, const std::string& text) {
  return out.find(text) != std::string::npos;
}

TEST(AssertionLabelScopes, DISABLED_AnElseBlockVariableIsReachedThroughLabels) {
  SimFixture f;
  EXPECT_EQ(
      LabelScopeRun("  initial begin : B1\n    #1;\n"
                    "    A1: assert (b) else begin : B2\n      bit d;\n"
                    "      d = 1;\n    end\n  end\n",
                    "  initial #2 $display(\"%b %b\", top.m_i.B1.A1.B2.d, "
                    "m_i.B1.A1.B2.d);\n",
                    f),
      "1 1\n");
}

constexpr const char* kUnlabelledActionBlock =
    "  assert property (@(posedge clk) a |-> b) else begin : B3\n"
    "    static bit d = 0;\n"
    "    A5: assert (d) else $display(\"fail A5\");\n  end\n";

TEST(AssertionLabelScopes, DISABLED_AnUnlabelledAssertionsActionBlockIsAScope) {
  SimFixture f;
  EXPECT_TRUE(
      Has(LabelScopeRun(kUnlabelledActionBlock,
                        "  initial #1 $display(\"d %b\", m_i.B3.d);\n", f),
          "d 0\n"));
}

TEST(AssertionLabelScopes, ALabelInAnUnlabelledAssertionsActionBlock) {
  SimFixture f;
  EXPECT_FALSE(
      Has(LabelScopeRun(kUnlabelledActionBlock,
                        "  initial $assertoff(0, top.m_i.B3.A5);\n", f),
          "fail A5"));
  SimFixture g;
  EXPECT_TRUE(Has(LabelScopeRun(kUnlabelledActionBlock, "", g), "fail A5"));
}

constexpr const char* kCoverInANamedBlock =
    "  always_ff @(posedge clk) begin : B2\n    static logic f;\n"
    "    f <= a && c;\n    C3: cover property (f) begin\n"
    "      A4: assert (b) else $display(\"fail A4\");\n    end\n  end\n";

TEST(AssertionLabelScopes, ALabelledCoverInANamedBlockIsALevel) {
  SimFixture f;
  EXPECT_FALSE(
      Has(LabelScopeRun(kCoverInANamedBlock,
                        "  initial $assertoff(0, top.m_i.B2.C3.A4);\n", f),
          "fail A4"));
  SimFixture g;
  EXPECT_TRUE(Has(LabelScopeRun(kCoverInANamedBlock, "", g), "fail A4"));
}

constexpr const char* kCoverInAnEmptyUnnamedBlock =
    "  logic e;\n  always_ff @(posedge clk) begin\n    e <= a && c;\n"
    "    C1: cover property (e) begin\n"
    "      A2: assert (b) else $display(\"fail A2\");\n    end\n  end\n";

TEST(AssertionLabelScopes, AnUnnamedBlockDeclaringNothingAddsNoLevel) {
  SimFixture f;
  EXPECT_FALSE(
      Has(LabelScopeRun(kCoverInAnEmptyUnnamedBlock,
                        "  initial $assertoff(0, top.m_i.C1.A2);\n", f),
          "fail A2"));
  SimFixture g;
  EXPECT_TRUE(
      Has(LabelScopeRun(kCoverInAnEmptyUnnamedBlock, "", g), "fail A2"));
}

TEST(AssertionLabelScopes, DISABLED_ALabelUnderADeclaringUnnamedBlockIsHidden) {
  SimFixture f;
  LabelScopeRun(
      "  always_ff @(posedge clk) begin\n    static logic f;\n"
      "    f <= a && c;\n    C2: cover property (f) begin\n"
      "      A3: assert (a);\n    end\n  end\n",
      "  initial $assertoff(0, top.m_i.C2.A3);\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(AssertionLabelScopes, DISABLED_AnUnnamedActionBlocksVariableIsHidden) {
  SimFixture f;
  LabelScopeRun(
      "  initial begin : B1\n    A1: assert (a) begin\n      bit d;\n"
      "      d = 1;\n    end\n  end\n",
      "  initial #1 $display(\"%b\", top.m_i.B1.A1.d);\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(AssertionLabelScopes, AnAssertionLabelNamesItInAControlTask) {
  SimFixture f;
  std::string out = LabelScopeRun(
      "  initial begin : B1\n    #1;\n"
      "    A1: assert (b) else $display(\"fail A1\");\n"
      "    assert (b) else $display(\"fail anon\");\n  end\n",
      "  initial $assertoff(0, top.m_i.B1.A1);\n", f);
  EXPECT_FALSE(Has(out, "fail A1"));
  EXPECT_TRUE(Has(out, "fail anon"));
}

constexpr const char* kCheckerUnderReference =
    "checker chk(input logic clk);\n"
    "  bit a;\n"
    "  bit pass, fail, captured;\n"
    "  function bit f();\n"
    "    return a;\n"
    "  endfunction\n"
    "endchecker\n";

size_t CheckerReferenceReports(const std::string& items_or_design,
                               bool whole_design, uint32_t line) {
  SimFixture f;
  std::string src = whole_design
                        ? std::string(kCheckerUnderReference) + items_or_design
                        : std::string(kCheckerUnderReference) +
                              "module top;\n  logic clk, y, z;\n"
                              "  int n;\n  chk my_check(clk);\n" +
                              items_or_design + "endmodule\n";
  ElaborateSrcAllTops(src, f);
  const std::vector<Diagnostic>& diags = f.diag.Diagnostics();
  size_t n = 0;
  for (const auto& d : diags) {
    if (d.severity == DiagSeverity::kError && d.loc.line == line &&
        d.subclause == "23.6" &&
        d.message == "hierarchical reference into a checker is not permitted") {
      ++n;
    }
  }
  return n;
}

TEST(CheckerReferencePositions, NonblockingWrite) {
  EXPECT_EQ(CheckerReferenceReports(
                "  always @(posedge clk) my_check.a <= y;\n", false, 12),
            1u);
}

TEST(CheckerReferencePositions, NonblockingRead) {
  EXPECT_EQ(CheckerReferenceReports(
                "  always @(posedge clk) z <= my_check.a;\n", false, 12),
            1u);
}

TEST(CheckerReferencePositions, AlwaysComb) {
  EXPECT_EQ(
      CheckerReferenceReports("  always_comb z = my_check.a;\n", false, 12),
      1u);
}

TEST(CheckerReferencePositions, AlwaysLatch) {
  EXPECT_EQ(CheckerReferenceReports("  always_latch if (y) z = my_check.a;\n",
                                    false, 12),
            1u);
}

TEST(CheckerReferencePositions, AlwaysFf) {
  EXPECT_EQ(CheckerReferenceReports(
                "  always_ff @(posedge clk) z <= my_check.a;\n", false, 12),
            1u);
}

TEST(CheckerReferencePositions, Force) {
  EXPECT_EQ(CheckerReferenceReports("  initial force my_check.a = 1'b1;\n",
                                    false, 12),
            1u);
}

TEST(CheckerReferencePositions, Release) {
  EXPECT_EQ(
      CheckerReferenceReports("  initial release my_check.a;\n", false, 12),
      1u);
}

TEST(CheckerReferencePositions, ProceduralAssign) {
  EXPECT_EQ(
      CheckerReferenceReports("  initial assign my_check.a = y;\n", false, 12),
      1u);
}

TEST(CheckerReferencePositions, Deassign) {
  EXPECT_EQ(
      CheckerReferenceReports("  initial deassign my_check.a;\n", false, 12),
      1u);
}

TEST(CheckerReferencePositions, DISABLED_PostIncrement) {
  EXPECT_EQ(CheckerReferenceReports("  initial my_check.a++;\n", false, 12),
            1u);
}

TEST(CheckerReferencePositions, DISABLED_PostDecrement) {
  EXPECT_EQ(CheckerReferenceReports("  initial my_check.a--;\n", false, 12),
            1u);
}

TEST(CheckerReferencePositions, DISABLED_PreIncrement) {
  EXPECT_EQ(CheckerReferenceReports("  initial ++my_check.a;\n", false, 12),
            1u);
}

TEST(CheckerReferencePositions, DISABLED_PreDecrement) {
  EXPECT_EQ(CheckerReferenceReports("  initial --my_check.a;\n", false, 12),
            1u);
}

TEST(CheckerReferencePositions, DISABLED_IfCondition) {
  EXPECT_EQ(
      CheckerReferenceReports("  initial if (my_check.a) z = 1;\n", false, 12),
      1u);
}

TEST(CheckerReferencePositions, DISABLED_CaseExpression) {
  EXPECT_EQ(
      CheckerReferenceReports(
          "  initial case (my_check.a) 1: z = 1; default: z = 0; endcase\n",
          false, 12),
      1u);
}

TEST(CheckerReferencePositions, DISABLED_EventControl) {
  EXPECT_EQ(
      CheckerReferenceReports("  initial @(my_check.a) z = 1;\n", false, 12),
      1u);
}

TEST(CheckerReferencePositions, DISABLED_SystemTaskArgument) {
  EXPECT_EQ(CheckerReferenceReports(
                "  initial $display(\"%0d\", my_check.a);\n", false, 12),
            1u);
}

TEST(CheckerReferencePositions, DISABLED_TaskBody) {
  EXPECT_EQ(CheckerReferenceReports("  task t;\n"
                                    "    z = my_check.a;\n"
                                    "  endtask\n",
                                    false, 13),
            1u);
}

TEST(CheckerReferencePositions, DISABLED_FunctionBody) {
  EXPECT_EQ(CheckerReferenceReports("  function bit g();\n"
                                    "    return my_check.a;\n"
                                    "  endfunction\n",
                                    false, 13),
            1u);
}

TEST(CheckerReferencePositions, DISABLED_ClassMethod) {
  EXPECT_EQ(CheckerReferenceReports("  class c;\n"
                                    "    function bit g();\n"
                                    "      return my_check.a;\n"
                                    "    endfunction\n"
                                    "  endclass\n",
                                    false, 14),
            1u);
}

TEST(CheckerReferencePositions, DISABLED_GenerateAlways) {
  EXPECT_EQ(
      CheckerReferenceReports("  if (1) begin : gb\n"
                              "    always @(posedge clk) z = my_check.a;\n"
                              "  end\n",
                              false, 13),
      1u);
}

TEST(CheckerReferencePositions, DISABLED_GenerateAssign) {
  EXPECT_EQ(CheckerReferenceReports("  if (1) begin : gb\n"
                                    "    assign z = my_check.a;\n"
                                    "  end\n",
                                    false, 13),
            1u);
}

TEST(CheckerReferencePositions, Interface) {
  EXPECT_EQ(CheckerReferenceReports("interface ifc;\n"
                                    "  logic clk, z;\n"
                                    "  chk my_check(clk);\n"
                                    "  always @(posedge clk) z = my_check.a;\n"
                                    "endinterface\n"
                                    "module top;\n"
                                    "  ifc i();\n"
                                    "endmodule\n",
                                    true, 11),
            1u);
}

TEST(CheckerReferencePositions, Program) {
  EXPECT_EQ(CheckerReferenceReports("program prg;\n"
                                    "  logic clk, z;\n"
                                    "  chk my_check(clk);\n"
                                    "  initial z = my_check.a;\n"
                                    "endprogram\n"
                                    "module top;\n"
                                    "  prg p();\n"
                                    "endmodule\n",
                                    true, 11),
            1u);
}

TEST(CheckerReferencePositions, CheckerInChecker) {
  EXPECT_EQ(CheckerReferenceReports("checker outer(input logic clk);\n"
                                    "  bit b;\n"
                                    "  chk inner(clk);\n"
                                    "  always_ff @(posedge clk) b <= inner.a;\n"
                                    "endchecker\n"
                                    "module top;\n"
                                    "  logic clk;\n"
                                    "  outer o(clk);\n"
                                    "endmodule\n",
                                    true, 11),
            1u);
}

TEST(CheckerReferencePositions, DISABLED_TopLevelInstanceName) {
  EXPECT_EQ(CheckerReferenceReports(
                "  initial #50 $display(\"%0d\", my_check.pass);\n", false, 12),
            1u);
}

TEST(CheckerReferencePositions, DISABLED_LoopGenerateBlock) {
  EXPECT_EQ(
      CheckerReferenceReports("module top;\n"
                              "  logic clk;\n"
                              "  for (genvar i = 0; i < 3; i++) begin : g\n"
                              "    chk c(clk);\n"
                              "  end\n"
                              "  initial #52 $display(\"%0d\", g[0].c.pass);\n"
                              "endmodule\n",
                              true, 13),
      1u);
}

TEST(CheckerReferencePositions, DISABLED_ConditionalGenerateBlock) {
  EXPECT_EQ(
      CheckerReferenceReports("module top;\n"
                              "  logic clk;\n"
                              "  if (1) begin : g\n"
                              "    chk c(clk);\n"
                              "  end\n"
                              "  initial #50 $display(\"%0d\", g.c.pass);\n"
                              "endmodule\n",
                              true, 13),
      1u);
}

TEST(CheckerReferencePositions, DISABLED_FromAnotherTop) {
  EXPECT_EQ(
      CheckerReferenceReports("module top;\n"
                              "  logic clk;\n"
                              "  chk ci(clk);\n"
                              "endmodule\n"
                              "module other;\n"
                              "  initial $display(\"%0d\", top.ci.pass);\n"
                              "endmodule\n",
                              true, 13),
      1u);
}

TEST(CheckerReferencePositions, DISABLED_Rooted) {
  EXPECT_EQ(
      CheckerReferenceReports(
          "  initial $display(\"%0d\", $root.top.my_check.pass);\n", false, 12),
      1u);
}

TEST(CheckerReferencePositions, DISABLED_TopNamed) {
  EXPECT_EQ(CheckerReferenceReports(
                "  initial $display(\"%0d\", top.my_check.pass);\n", false, 12),
            1u);
}

TEST(CheckerReferencePositions, DISABLED_ThroughAChildFullPath) {
  EXPECT_EQ(CheckerReferenceReports("module mid(input logic clk);\n"
                                    "  chk cm(clk);\n"
                                    "endmodule\n"
                                    "module top;\n"
                                    "  logic clk, x;\n"
                                    "  mid mi(clk);\n"
                                    "  assign x = top.mi.cm.captured;\n"
                                    "endmodule\n",
                                    true, 14),
            1u);
}

TEST(CheckerReferencePositions, DISABLED_ThroughAChild) {
  EXPECT_EQ(CheckerReferenceReports("module mid(input logic clk);\n"
                                    "  chk cm(clk);\n"
                                    "endmodule\n"
                                    "module top;\n"
                                    "  logic clk, x;\n"
                                    "  mid mi(clk);\n"
                                    "  assign x = mi.cm.captured;\n"
                                    "endmodule\n",
                                    true, 14),
            1u);
}

TEST(CheckerReferencePositions, DISABLED_FunctionCallThroughAChild) {
  EXPECT_EQ(CheckerReferenceReports("module mid(input logic clk);\n"
                                    "  chk cm(clk);\n"
                                    "endmodule\n"
                                    "module top;\n"
                                    "  logic clk;\n"
                                    "  bit w;\n"
                                    "  mid mi(clk);\n"
                                    "  initial w = mi.cm.f();\n"
                                    "endmodule\n",
                                    true, 15),
            1u);
}

TEST(CheckerReferencePositions, DISABLED_CompoundAssignment) {
  EXPECT_EQ(CheckerReferenceReports("  initial my_check.a += y;\n", false, 12),
            1u);
}

TEST(CheckerReferencePositions, ACheckersOwnVariableByItsSimpleName) {
  EXPECT_EQ(CheckerReferenceReports(
                "checker inner(input logic clk);\n  bit a, b;\n"
                "  always_ff @(posedge clk) b <= a;\nendchecker\n"
                "module top;\n  logic clk;\n  inner i(clk);\nendmodule\n",
                true, 10),
            0u);
}

constexpr const char* kOtherTop =
    "module m;\n"
    "  logic clk = 0;\n"
    "  int v = 0;\n"
    "  function int pn();\n"
    "    return 0;\n"
    "  endfunction\n"
    "  initial repeat (4) #5 clk = ~clk;\n"
    "endmodule\n";

bool ElaboratesClean(const std::string& src) {
  SimFixture f;
  ElaborateSrcAllTops(src, f);
  return !f.diag.HasErrors();
}

TEST(AssertionHierarchicalNames, DISABLED_ClockingEventIntoAnotherTop) {
  EXPECT_TRUE(ElaboratesClean(std::string(kOtherTop) +
                              "module t;\n"
                              "  ta: assert property (@(posedge m.clk) 1);\n"
                              "endmodule\n"));
}

TEST(AssertionHierarchicalNames, DISABLED_ExpressionVariableIntoAnotherTop) {
  EXPECT_TRUE(ElaboratesClean(std::string(kOtherTop) +
                              "module t;\n"
                              "  logic c = 0;\n"
                              "  ta: assert property (@(posedge c) m.v == 0);\n"
                              "endmodule\n"));
}

TEST(AssertionHierarchicalNames, DISABLED_ExpressionFunctionIntoAnotherTop) {
  EXPECT_TRUE(
      ElaboratesClean(std::string(kOtherTop) +
                      "module t;\n"
                      "  logic c = 0;\n"
                      "  ta: assert property (@(posedge c) m.pn() == 0);\n"
                      "endmodule\n"));
}

TEST(AssertionHierarchicalNames, DISABLED_ProgramClockingEvent) {
  EXPECT_TRUE(ElaboratesClean(std::string(kOtherTop) +
                              "program p;\n"
                              "  pa: assert property (@(posedge m.clk) 1);\n"
                              "endprogram\n"));
}

TEST(AssertionHierarchicalNames, DISABLED_ProgramExpression) {
  EXPECT_TRUE(ElaboratesClean(std::string(kOtherTop) +
                              "program p;\n"
                              "  logic c = 0;\n"
                              "  pa: assert property (@(posedge c) m.v == 0);\n"
                              "endprogram\n"));
}

TEST(AssertionHierarchicalNames, DISABLED_UpwardFromAnInterface) {
  EXPECT_TRUE(ElaboratesClean(
      "interface ifc(input logic clk);\n"
      "  ia: assert property (@(posedge clk) top.v == top.pn());\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  int v = 0;\n"
      "  function int pn();\n"
      "    return 0;\n"
      "  endfunction\n"
      "  ifc i(clk);\n"
      "endmodule\n"));
}

TEST(AssertionHierarchicalNames, DISABLED_UpwardFromAChecker) {
  EXPECT_TRUE(ElaboratesClean(
      "checker chk(input logic clk);\n"
      "  ca: assert property (@(posedge clk) top.v == top.pn());\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  int v = 0;\n"
      "  function int pn();\n"
      "    return 0;\n"
      "  endfunction\n"
      "  chk c(clk);\n"
      "endmodule\n"));
}

TEST(AssertionHierarchicalNames, DISABLED_UpwardFromAModuleInstance) {
  EXPECT_TRUE(ElaboratesClean(
      "module leaf(input logic clk);\n"
      "  la: assert property (@(posedge clk) top.v == top.pn());\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  int v = 0;\n"
      "  function int pn();\n"
      "    return 0;\n"
      "  endfunction\n"
      "  leaf l(clk);\n"
      "endmodule\n"));
}

TEST(AssertionHierarchicalNames, ProceduralAssertion) {
  EXPECT_TRUE(
      ElaboratesClean(std::string(kOtherTop) +
                      "module t;\n"
                      "  logic c = 0;\n"
                      "  always @(posedge c) assert property (m.v == 0);\n"
                      "endmodule\n"));
}

TEST(AssertionHierarchicalNames, DISABLED_AssumeProperty) {
  EXPECT_TRUE(ElaboratesClean(std::string(kOtherTop) +
                              "module t;\n"
                              "  logic c = 0;\n"
                              "  assume property (@(posedge c) m.v == 0);\n"
                              "endmodule\n"));
}

TEST(AssertionHierarchicalNames, DISABLED_CoverProperty) {
  EXPECT_TRUE(ElaboratesClean(std::string(kOtherTop) +
                              "module t;\n"
                              "  logic c = 0;\n"
                              "  cover property (@(posedge c) m.v == 0);\n"
                              "endmodule\n"));
}

TEST(AssertionHierarchicalNames, DISABLED_CoverSequence) {
  EXPECT_TRUE(ElaboratesClean(std::string(kOtherTop) +
                              "module t;\n"
                              "  logic c = 0;\n"
                              "  cover sequence (@(posedge c) m.v == 0);\n"
                              "endmodule\n"));
}

TEST(AssertionHierarchicalNames, DISABLED_SequenceDeclarationBody) {
  EXPECT_TRUE(ElaboratesClean(std::string(kOtherTop) +
                              "module t;\n"
                              "  logic c = 0;\n"
                              "  sequence s;\n"
                              "    m.v == 0;\n"
                              "  endsequence\n"
                              "  assert property (@(posedge c) s);\n"
                              "endmodule\n"));
}

TEST(AssertionHierarchicalNames, DISABLED_PropertyDeclarationBody) {
  EXPECT_TRUE(ElaboratesClean(std::string(kOtherTop) +
                              "module t;\n"
                              "  logic c = 0;\n"
                              "  property q;\n"
                              "    m.v == 0;\n"
                              "  endproperty\n"
                              "  assert property (@(posedge c) q);\n"
                              "endmodule\n"));
}

TEST(AssertionHierarchicalNames, DISABLED_GenerateBlockVariable) {
  EXPECT_TRUE(
      ElaboratesClean("module t;\n"
                      "  logic c = 0;\n"
                      "  if (1) begin : g\n"
                      "    logic x = 1;\n"
                      "  end\n"
                      "  assert property (@(posedge c) g.x);\n"
                      "endmodule\n"));
}

TEST(AssertionHierarchicalNames, AFirstComponentNamingNothingIsReported) {
  SimFixture f;
  ElaborateSrcAllTops(
      "module t;\n  logic c = 0;\n"
      "  assert property (@(posedge c) nosuch.v == 0);\nendmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'nosuch'", 3,
                            "23.9"));
}

TEST(HierarchicalNameTree, LikeNamedPropertiesOfTwoClassesKeepTheirOwn) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n  class a;\n    int p = 1;\n  endclass\n"
                       "  class b;\n    int p = 2;\n  endclass\n"
                       "  a x;\n  b y;\n"
                       "  initial begin\n    x = new;\n    y = new;\n"
                       "    $display(\"%0d %0d\", x.p, y.p);\n  end\n"
                       "endmodule\n",
                       f),
            "1 2\n");
}

}  // namespace
