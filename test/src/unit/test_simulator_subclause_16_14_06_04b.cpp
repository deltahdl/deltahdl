#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_placed_assertion_runs.h"

using namespace delta;

namespace {

std::string DisableSource(const std::string& procedures) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic a = 1, b = 1;\n"
         "  int go = 0, go2 = 0;\n"
         "  logic clear_b2 = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  default clocking @(posedge clk); endclocking\n" +
         procedures +
         "  initial begin\n"
         "    #10 go = 1;\n"
         "    #10 go = 2;\n"
         "    #10 go2 = 1;\n"
         "    clear_b2 = 1;\n"
         "    #10 go2 = 2;\n"
         "    #1 clear_b2 = 0;\n"
         "    #9 $finish;\n"
         "  end\n"
         "endmodule\n";
}

TEST(DisablingProceduralAssertionsRun,
     ASpecificDisableClearsThatAssertionsPendingInstancesAlone) {
  SimFixture f;
  std::string out =
      RunCapture(DisableSource("  always @(go) begin : b1\n"
                               "    a1: assert property (const'(a))\n"
                               "      $display(\"a1 passed at %0d\", $time);\n"
                               "    a2: assert property (const'(b))\n"
                               "      $display(\"a2 passed at %0d\", $time);\n"
                               "    if (go == 2) disable a1;\n"
                               "    else begin\n"
                               "      #1 disable a1;\n"
                               "    end\n"
                               "  end\n"),
                 f);
  EXPECT_EQ(out,
            "a1 passed at 15\na2 passed at 15\na2 passed at 25\n"
            "$finish at time 50\n");
}

TEST(DisablingProceduralAssertionsRun,
     ADisableOfTheOutermostScopeFlushesThePendingQueue) {
  SimFixture f;
  std::string out =
      RunCapture(DisableSource("  always @(go2) begin : b2\n"
                               "    a3: assert property (const'(a))\n"
                               "      $display(\"a3 passed at %0d\", $time);\n"
                               "    a4: assert property (const'(b))\n"
                               "      $display(\"a4 passed at %0d\", $time);\n"
                               "  end\n"
                               "  always @(clear_b2) begin : b3\n"
                               "    disable b2;\n"
                               "  end\n"),
                 f);
  EXPECT_EQ(out, "a3 passed at 45\na4 passed at 45\n$finish at time 50\n");
}

std::string Checked(const std::string& name, const std::string& directive,
                    const std::string& expr, const std::string& shown) {
  return "    " + name + ": " + directive + " (@(posedge clk) " + expr +
         ")\n      $display(\"%s " + shown + " passed at %0d\", tag, $time);\n";
}

std::string Checked(const std::string& name, const std::string& directive,
                    const std::string& expr) {
  return Checked(name, directive, expr, name);
}

std::string Asserted(const std::string& name, const std::string& expr) {
  return Checked(name, "assert property", expr);
}

std::string PlacedDisableSource(const std::string& place,
                                const std::string& procedures) {
  std::string body = "  string tag = \"" + place + "\";\n" + procedures;
  std::string top =
      "  logic clk = 0, a = 1, b = 1;\n"
      "  int go = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  initial begin #10 go = 1; #10 go = 2; #20 $finish; end\n";
  if (place == "module") return "module t;\n" + top + body + "endmodule\n";
  if (place == "generate") {
    return "module t;\n" + top + "  if (1) begin : g\n" + body +
           "  end\nendmodule\n";
  }
  return "interface w(input logic clk, a, b, input var int go);\n" + body +
         "endinterface\nmodule t;\n" + top + "  w u(clk, a, b, go);\n" +
         "endmodule\n";
}

std::string PlacedTagged(const std::string& lines, const std::string& place) {
  std::string out;
  for (const std::string& line : PlacedLines(lines)) {
    out.append(place).append(" ").append(line).append("\n");
  }
  return PlacedSorted(PlacedLines(out));
}

void ExpectDisableInEachPlace(const std::string& procedures,
                              const std::string& want) {
  for (const char* place : {"module", "generate", "interface"}) {
    std::string src = PlacedDisableSource(place, procedures);
    SCOPED_TRACE(src);
    SimFixture f;
    EXPECT_EQ(PlacedSortedVerdicts(RunCapture(src, f)),
              PlacedTagged(want, place));
  }
}

TEST(DisablingProceduralAssertionsRun,
     DISABLED_AHierarchicalDisableClearsAnotherProceduresAssertion) {
  ExpectDisableInEachPlace(
      "  always @(go) begin : b1\n" + Asserted("a1", "const'(a)") +
          Asserted("a2", "const'(b)") +
          "  end\n"
          "  always @(go) begin : b2\n" +
          Checked("a1", "assert property", "const'(a)", "b2.a1") +
          "    if (go == 1) #0 disable b1.a1;\n"
          "  end\n",
      "b2.a1 passed at 15\na2 passed at 15\n"
      "a1 passed at 25\nb2.a1 passed at 25\n"
      "a2 passed at 25\n");
}

TEST(DisablingProceduralAssertionsRun,
     DISABLED_ADisableFromAProcedureWithoutAssertionsClearsTheNamedOne) {
  ExpectDisableInEachPlace("  always @(go) begin : b1\n" +
                               Asserted("a1", "const'(a)") +
                               Asserted("a2", "const'(b)") +
                               "  end\n"
                               "  initial begin #10; #0 disable b1.a1; end\n",
                           "a2 passed at 15\na1 passed at 25\n"
                           "a2 passed at 25\n");
}

TEST(DisablingProceduralAssertionsRun,
     DISABLED_ADisableOfOneInstancesAssertionLeavesTheOtherInstances) {
  std::string src =
      "module m #(parameter int D = 0)(input logic clk, a, input var int go);\n"
      "  always @(go) begin : b1\n"
      "    a1: assert property (@(posedge clk) const'(a))\n"
      "      $display(\"u%0d a1 passed at %0d\", D + 1, $time);\n"
      "    if (D == 1 && go == 1) #0 disable t.u1.b1.a1;\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  logic clk = 0, a = 1;\n"
      "  int go = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  m #(0) u1(clk, a, go);\n"
      "  m #(1) u2(clk, a, go);\n"
      "  initial begin #10 go = 1; #10 go = 2; #20 $finish; end\n"
      "endmodule\n";
  SimFixture f;
  EXPECT_EQ(PlacedSortedVerdicts(RunCapture(src, f)),
            PlacedSorted({"u2 a1 passed at 15", "u1 a1 passed at 25",
                          "u2 a1 passed at 25"}));
}

TEST(DisablingProceduralAssertionsRun,
     AHierarchicalDisableFromTheOwnProcedureClearsThatAssertionAlone) {
  ExpectDisableInEachPlace("  always @(go) begin : b1\n" +
                               Asserted("a1", "const'(a)") +
                               Asserted("a2", "const'(b)") +
                               "    if (go == 1) #0 disable b1.a1;\n"
                               "  end\n",
                           "a2 passed at 15\na1 passed at 25\n"
                           "a2 passed at 25\n");
}

TEST(DisablingProceduralAssertionsRun,
     ASpecificDisableClearsEachKindOfAssertionAlone) {
  for (const char* directive :
       {"assume property", "cover property", "cover sequence"}) {
    SCOPED_TRACE(directive);
    ExpectDisableInEachPlace("  always @(go) begin : b1\n" +
                                 Checked("x1", directive, "const'(a)") +
                                 Asserted("a2", "const'(b)") +
                                 "    if (go == 1) disable x1;\n"
                                 "  end\n",
                             "a2 passed at 15\nx1 passed at 25\n"
                             "a2 passed at 25\n");
  }
}

TEST(DisablingProceduralAssertionsRun,
     ASpecificDisableClearsEveryPendingInstanceOfTheAssertion) {
  ExpectDisableInEachPlace(
      "  always @(go) begin : b1\n"
      "    repeat (2)\n" +
          Asserted("a1", "const'(a)") + Asserted("a2", "const'(b)") +
          "    if (go == 1) disable a1;\n"
          "  end\n",
      "a2 passed at 15\na1 passed at 25\n"
      "a1 passed at 25\na2 passed at 25\n");
}

TEST(DisablingProceduralAssertionsRun,
     AProcedureDisablingItsOwnOutermostScopeFlushesItsQueue) {
  ExpectDisableInEachPlace("  always @(go) begin : b1\n" +
                               Asserted("a1", "const'(a)") +
                               Asserted("a2", "const'(b)") +
                               "    if (go == 1) #0 disable b1;\n"
                               "  end\n",
                           "a1 passed at 25\na2 passed at 25\n");
}

TEST(DisablingProceduralAssertionsRun,
     ADisableOfTheOutermostScopeFlushesInitialAndAlwaysCombQueues) {
  ExpectDisableInEachPlace(
      "  int x;\n"
      "  initial begin : i1\n"
      "    #10;\n" +
          Asserted("a1", "const'(a)") +
          "    #3;\n"
          "  end\n"
          "  always_comb begin : c1\n" +
          Asserted("a2", "const'(b)") +
          "    x = go;\n"
          "  end\n"
          "  initial begin\n"
          "    #10;\n"
          "    #0 disable i1;\n"
          "    disable c1;\n"
          "  end\n",
      "a2 passed at 5\na2 passed at 25\n");
}

TEST(DisablingProceduralAssertionsRun,
     ADisableOfTheOutermostScopeFlushesAssertionsOfNestedBlocks) {
  ExpectDisableInEachPlace(
      "  always @(go) begin : b1\n"
      "    begin : inner\n" +
          Asserted("a1", "const'(a)") + "    end\n" +
          Asserted("a2", "const'(b)") +
          "  end\n"
          "  initial begin #10; #0 disable b1; end\n",
      "a1 passed at 25\na2 passed at 25\n");
}

TEST(DisablingProceduralAssertionsRun,
     AnAttemptMaturedBeforeADisableRunsToItsPass) {
  for (const char* target : {"b1", "b1.a1"}) {
    SCOPED_TRACE(target);
    ExpectDisableInEachPlace(
        "  always @(go) begin : b1\n"
        "    if (go == 1)\n" +
            Asserted("a1", "const'(a) ##2 b") +
            "  end\n"
            "  initial begin #20; disable " +
            target + "; end\n",
        "a1 passed at 35\n");
  }
}

TEST(DisablingProceduralAssertionsRun,
     ADisableOfAnInnerBlockFlushesNoPendingInstance) {
  ExpectDisableInEachPlace(
      "  always @(go) begin : b1\n" + Asserted("a1", "const'(a)") +
          "    begin : inner\n" + Asserted("a2", "const'(b)") +
          "      if (go == 1) disable inner;\n"
          "      #3;\n"
          "    end\n"
          "  end\n"
          "  always @(go) begin : b2\n"
          "    begin : inner\n" +
          Asserted("a3", "const'(a)") +
          "      #3;\n"
          "    end\n"
          "  end\n"
          "  initial begin #10; #0 disable b2.inner; end\n",
      "a1 passed at 15\na2 passed at 15\n"
      "a3 passed at 15\na1 passed at 25\n"
      "a2 passed at 25\na3 passed at 25\n");
}

TEST(DisablingProceduralAssertionsRun,
     ADisableOfATaskFlushesNoPendingInstance) {
  ExpectDisableInEachPlace(
      "  task automatic hold;\n"
      "    #3;\n"
      "  endtask\n"
      "  task automatic quit;\n"
      "    disable quit;\n"
      "  endtask\n"
      "  always @(go) begin : b1\n" +
          Asserted("a1", "const'(a)") +
          "    quit();\n"
          "    hold();\n"
          "  end\n"
          "  initial begin #10; #0 disable hold; end\n",
      "a1 passed at 15\na1 passed at 25\n");
}

}  // namespace
