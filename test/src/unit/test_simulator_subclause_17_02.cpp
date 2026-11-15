#include <gtest/gtest.h>

#include <string>

#include "helpers_placed_assertion_runs.h"

using namespace delta;

namespace {

const char* const kStimulus =
    "  logic clk = 0, a = 1, x = 1, y = 0, rst = 0;\n"
    "  logic [3:0] v = 4'b1111;\n"
    "  always #5 clk = ~clk;\n"
    "  initial begin\n"
    "    #10 rst = 1;\n"
    "    #2 a = 0; x = 0; y = 1; v[2] = 0;\n"
    "    #10 rst = 0; v[2] = 1;\n"
    "    #10 a = 1; y = 0; v[0] = 0;\n"
    "    #10 x = 1; v[0] = 1;\n"
    "    #8 $finish;\n"
    "  end\n";

std::string RunBody(const std::string& body) {
  std::string src =
      "checker c(input logic clk, input logic a, input logic x,\n"
      "          input logic y, input logic rst, input logic [3:0] v);\n" +
      body +
      "endchecker\n"
      "module t;\n" +
      kStimulus +
      "  c u(clk, a, x, y, rst, v);\n"
      "endmodule\n";
  return PlacedSortedVerdicts(RunPlaced(src).lines);
}

TEST(CheckerBodyItemsRun, AnAssumptionIsCheckedAsAnAssertion) {
  EXPECT_EQ(RunBody("  m1: assume property (@(posedge clk) a)\n"
                    "    else $display(\"m1 %0t\", $time);\n"),
            "m1 15\nm1 25\n");
}

TEST(CheckerBodyItemsRun, ACoverSequenceRunsItsPassActionAtEachMatch) {
  EXPECT_EQ(RunBody("  c1: cover sequence (@(posedge clk) a ##1 !a)\n"
                    "    $display(\"c1 %0t\", $time);\n"),
            "c1 15\n");
}

TEST(CheckerBodyItemsRun, AnObservedDeferredAssertionReportsOnceSettled) {
  EXPECT_EQ(RunBody("  a1: assert #0 (x != y) else $display(\"a1 %0t\", "
                    "$time);\n"),
            "a1 32\n");
}

TEST(CheckerBodyItemsRun, ADeferredCoverAndAssumeRunAsDeferred) {
  EXPECT_EQ(RunBody("  c1: cover #0 (x) $display(\"c1 %0t\", $time);\n"
                    "  m1: assume #0 (x) else $display(\"m1 %0t\", $time);\n"),
            "c1 0\nc1 42\nm1 12\n");
}

TEST(CheckerBodyItemsRun, AFinalDeferredAssertionReportsOnceSettled) {
  EXPECT_EQ(RunBody("  a1: assert final (x != y) else $display(\"a1 %0t\", "
                    "$time);\n"),
            "a1 32\n");
}

TEST(CheckerBodyItemsRun, AnAssertionTakesTheDefaultClocking) {
  EXPECT_EQ(RunBody("  clocking cb @(posedge clk); endclocking\n"
                    "  default clocking cb;\n"
                    "  a1: assert property (a) else $display(\"a1 %0t\", "
                    "$time);\n"),
            "a1 15\na1 25\n");
}

TEST(CheckerBodyItemsRun, ADefaultDisableIffDisablesTheAssertions) {
  EXPECT_EQ(RunBody("  default disable iff rst;\n"
                    "  a1: assert property (@(posedge clk) a)\n"
                    "    else $display(\"a1 %0t\", $time);\n"),
            "a1 25\n");
}

TEST(CheckerBodyItemsRun, ALoopGenerateMakesOneAssertionPerBit) {
  EXPECT_EQ(RunBody("  for (genvar i = 0; i < 4; i++) begin : g\n"
                    "    a1: assert property (@(posedge clk) v[i])\n"
                    "      else $display(\"%m %0t\", $time);\n"
                    "  end\n"),
            "t.u.g[0].a1 35\nt.u.g[2].a1 15\n");
}

std::string DeclaredChecker(const std::string& place) {
  return "  checker c2(input logic clk, input logic a);\n"
         "    a2: assert property (@(posedge clk) a)\n"
         "      else $display(\"" +
         place +
         " %0t\", $time);\n"
         "  endchecker\n"
         "  c2 u2(clk, a);\n";
}

std::string RunDeclared(const std::string& before, const std::string& items) {
  std::string src = before + "module t;\n" + kStimulus + items + "endmodule\n";
  return PlacedSortedVerdicts(RunPlaced(src).lines);
}

std::string Container(const std::string& keyword, const std::string& head,
                      const std::string& body) {
  return keyword + " " + head + "(input logic clk, input logic a);\n" + body +
         "end" + keyword + "\n";
}

std::string Fails(const std::string& place) {
  return place + " 15\n" + place + " 25\n";
}

std::string InIfBlock(const std::string& place) {
  return "  if (1) begin : g\n" + DeclaredChecker(place) + "  end\n";
}

TEST(CheckerDeclarationPlacesRun, AnInterface) {
  EXPECT_EQ(RunDeclared(Container("interface", "ifc", DeclaredChecker("ifc")),
                        "  ifc i(clk, a);\n"),
            Fails("ifc"));
}

TEST(CheckerDeclarationPlacesRun, AProgram) {
  EXPECT_EQ(RunDeclared(Container("program", "prg", DeclaredChecker("prg")),
                        "  prg p(clk, a);\n"),
            Fails("prg"));
}

TEST(CheckerDeclarationPlacesRun, AChecker) {
  EXPECT_EQ(RunDeclared(Container("checker", "o", DeclaredChecker("chk")),
                        "  o u(clk, a);\n"),
            Fails("chk"));
}

TEST(CheckerDeclarationPlacesRun, DISABLED_AModulesIfGenerateBlock) {
  EXPECT_EQ(RunDeclared("", InIfBlock("if")), Fails("if"));
}

TEST(CheckerDeclarationPlacesRun, DISABLED_AModulesCaseGenerateBlock) {
  EXPECT_EQ(RunDeclared("", "  case (1) 1: begin : g\n" +
                                DeclaredChecker("case") + "  end endcase\n"),
            Fails("case"));
}

TEST(CheckerDeclarationPlacesRun, DISABLED_AModulesLoopGenerateBlock) {
  EXPECT_EQ(RunDeclared("", "  for (genvar i = 0; i < 2; i++) begin : g\n" +
                                DeclaredChecker("for") + "  end\n"),
            "for 15\nfor 15\nfor 25\nfor 25\n");
}

TEST(CheckerDeclarationPlacesRun, AModulesGenerateRegion) {
  EXPECT_EQ(RunDeclared("", "  generate\n" + DeclaredChecker("gen") +
                                "  endgenerate\n"),
            Fails("gen"));
}

TEST(CheckerDeclarationPlacesRun, DISABLED_AnInterfacesGenerateBlock) {
  EXPECT_EQ(RunDeclared(Container("interface", "ifc", InIfBlock("ifc")),
                        "  ifc i(clk, a);\n"),
            Fails("ifc"));
}

TEST(CheckerDeclarationPlacesRun, DISABLED_AProgramsGenerateBlock) {
  EXPECT_EQ(RunDeclared(Container("program", "prg", InIfBlock("prg")),
                        "  prg p(clk, a);\n"),
            Fails("prg"));
}

TEST(CheckerDeclarationPlacesRun, DISABLED_ACheckersGenerateBlock) {
  EXPECT_EQ(RunDeclared(Container("checker", "o", InIfBlock("chk")),
                        "  o u(clk, a);\n"),
            Fails("chk"));
}

}  // namespace
