#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <string>

#include "fixture_simulator.h"
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

std::string RunLines(const std::string& src) {
  return PlacedSortedVerdicts(RunPlaced(src).lines);
}

const char* const kCounter =
    "checker chk(input logic in, en = 1'b1, input logic clk,\n"
    "            output int ctr = 5);\n"
    "  always_ff @(posedge clk) begin\n"
    "    $display(\"ff %0t %0d\", $time, ctr);\n"
    "    if (en && in) ctr <= ctr + 1;\n"
    "  end\n"
    "endchecker\n";

std::string CounterTop(const std::string& items) {
  return std::string(kCounter) +
         "module t;\n"
         "  logic clk = 0, a = 1;\n"
         "  always #5 clk = ~clk;\n" +
         items + "  initial #21 $finish;\nendmodule\n";
}

TEST(CheckerOutputInitialValueRun, AVariableActualReadsTheInitialValue) {
  EXPECT_EQ(RunLines(CounterTop("  int c;\n"
                                "  chk u(a, , clk, c);\n"
                                "  initial begin #1 $display(\"t1 %0d\", c);\n"
                                "    #19 $display(\"t20 %0d\", c); end\n")),
            "ff 15 6\nff 5 5\nt1 5\nt20 7\n");
}

TEST(CheckerOutputInitialValueRun, ANetActualReadsTheInitialValue) {
  EXPECT_EQ(RunLines(CounterTop("  wire [31:0] w;\n"
                                "  chk u(a, , clk, w);\n"
                                "  initial begin #1 $display(\"t1 %0d\", w);\n"
                                "    #19 $display(\"t20 %0d\", w); end\n")),
            "ff 15 6\nff 5 5\nt1 5\nt20 7\n");
}

const char* const kHeld =
    "checker held(event clock, output int ctr = 7);\n"
    "  a1: assert property (@clock ctr < 5) else $display(\"a1 %0t\", "
    "$time);\n"
    "endchecker\n";

std::string HeldTop(const std::string& items) {
  return std::string(kHeld) +
         "module t;\n"
         "  logic clk = 0;\n"
         "  always #5 clk = ~clk;\n" +
         items + "  initial #21 $finish;\nendmodule\n";
}

TEST(CheckerOutputInitialValueRun, AnAssertionSamplesTheInitialValue) {
  EXPECT_EQ(RunLines(HeldTop("  int c;\n"
                             "  held u(posedge clk, c);\n"
                             "  initial begin #1 $display(\"t1 %0d\", c);\n"
                             "    #19 $display(\"t20 %0d\", c); end\n")),
            "a1 15\na1 5\nt1 7\nt20 7\n");
}

TEST(CheckerOutputInitialValueRun, AnUnconnectedOutputKeepsTheInitialValue) {
  EXPECT_EQ(RunLines(HeldTop("  held u(posedge clk, );\n"
                             "  initial #20 $display(\"u %0d\", u.ctr);\n")),
            "a1 15\na1 5\nu 7\n");
}

const char* const kKinds =
    "typedef enum logic [1:0] {A, B, C} st_t;\n"
    "typedef struct packed {logic [3:0] hi, lo;} ps_t;\n";

TEST(CheckerOutputInitialValueRun, AnInheritedOutputTakesItsOwnInitialValue) {
  EXPECT_EQ(RunLines("checker inh(output int a, b = 3); endchecker\n"
                     "module t;\n"
                     "  int x, y;\n"
                     "  inh u(x, y);\n"
                     "  initial #1 $display(\"%0d %0d\", x, y);\n"
                     "endmodule\n"),
            "0 3\n");
}

TEST(CheckerOutputInitialValueRun, EachSingularTypeKindTakesItsValue) {
  EXPECT_EQ(RunLines(std::string(kKinds) +
                     "checker kinds(output int a = 5, output bit [3:0] k = "
                     "4'h9,\n"
                     "              output ps_t p = '{4'h1, 4'h2},\n"
                     "              output st_t e = C);\n"
                     "endchecker\n"
                     "module t;\n"
                     "  int a; bit [3:0] k; ps_t p; st_t e;\n"
                     "  kinds u(a, k, p, e);\n"
                     "  initial #1 $display(\"%0d %0d %0d %0d\", a, k, p, e);\n"
                     "endmodule\n"),
            "5 9 18 2\n");
}

TEST(CheckerOutputInitialValueRun, AnOutputWithNoInitialValueTakesTheDefault) {
  EXPECT_EQ(
      RunLines("checker none(output int a, output logic [3:0] b);\n"
               "endchecker\n"
               "module t;\n"
               "  int a; logic [3:0] b;\n"
               "  none u(a, b);\n"
               "  initial #1 $display(\"%0d %b %0d %b\", a, b, u.a, u.b);\n"
               "endmodule\n"),
      "0 xxxx 0 xxxx\n");
}

const char* const kHeldCheckerBody =
    "  checker cv(output int ctr = 7); endchecker\n";

TEST(CheckerOutputInitialValueRun, APackageAndAUnitCheckerHandItOn) {
  EXPECT_EQ(RunLines(std::string("package pk;\n") + kHeldCheckerBody +
                     "endpackage\n" + kHeldCheckerBody +
                     "module t;\n"
                     "  int c, d;\n"
                     "  pk::cv up(c);\n"
                     "  cv uu(d);\n"
                     "  initial #1 $display(\"%0d %0d\", c, d);\n"
                     "endmodule\n"),
            "7 7\n");
}

TEST(CheckerOutputInitialValueRun, EachInstancePlaceHandsItOn) {
  EXPECT_EQ(
      RunLines(
          std::string(kHeldCheckerBody) +
          "interface ifc; int c; cv u(c); endinterface\n"
          "program prg; int c; cv u(c); initial #9 $display(\"prg %0d\", c);\n"
          "endprogram\n"
          "checker o; int c; cv u(c); endchecker\n"
          "module t;\n"
          "  logic clk = 0;\n"
          "  always #5 clk = ~clk;\n"
          "  int c, pc;\n"
          "  cv um(c);\n"
          "  ifc i();\n"
          "  prg p();\n"
          "  o uo();\n"
          "  if (1) begin : g int c; cv u(c); end\n"
          "  always @(posedge clk) cv up(pc);\n"
          "  initial begin\n"
          "    #7 $display(\"%0d %0d %0d %0d %0d\", c, i.c, uo.c, g.c, pc);\n"
          "  end\n"
          "endmodule\n"),
      "7 7 7 7 7\nprg 7\n");
}

TEST(CheckerFormalTypeInheritanceRun, AnInheritedPropertyRunsAsAProperty) {
  EXPECT_EQ(RunLines("checker chk(logic clk, property p, q);\n"
                     "  a1: assert property (@(posedge clk) p)\n"
                     "    else $display(\"p %0t\", $time);\n"
                     "  a2: assert property (@(posedge clk) q)\n"
                     "    else $display(\"q %0t\", $time);\n"
                     "endchecker\n"
                     "module t;\n"
                     "  logic clk = 0, a = 1, b = 0;\n"
                     "  always #5 clk = ~clk;\n"
                     "  chk u(clk, a |-> 1, a |-> b);\n"
                     "  initial #21 $finish;\n"
                     "endmodule\n"),
            "q 15\nq 5\n");
}

TEST(CheckerFormalTypeInheritanceRun, AnInheritedEventFiresOnItsActual) {
  EXPECT_EQ(RunLines("checker chk(event e1, e2);\n"
                     "  c2: cover property (@e2 1) $display(\"e2 %0t\", "
                     "$time);\n"
                     "endchecker\n"
                     "module t;\n"
                     "  event ev1, ev2;\n"
                     "  chk u(ev1, ev2);\n"
                     "  initial begin #3 ->ev1; #4 ->ev2; #6 ->ev1; #4 ->ev2;\n"
                     "    #3 $finish; end\n"
                     "endmodule\n"),
            "e2 17\ne2 7\n");
}

std::string RunWithFinals(const std::string& src) {
  SimFixture f;
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) {
    LowerAndRun(design, f);
    f.scheduler.EndSimulation();
  }
  std::cout.rdbuf(old_buf);
  return PlacedSortedVerdicts(captured.str());
}

std::string FinalBits(const std::string& formals, const std::string& shown,
                      const std::string& decls, const std::string& actuals) {
  return "typedef logic [6:0] w_t;\n"
         "typedef enum logic [2:0] {S0, S1, S2} st_t;\n"
         "checker chk(" +
         formals + ");\n  final $display(\"%0d %0d %0d\", " + shown +
         ");\nendchecker\nmodule t;\n" + decls + "  chk u(" + actuals +
         ");\n  initial #1 $finish;\nendmodule\n";
}

TEST(CheckerFormalTypeInheritanceRun, ADataTypeCarriesAlongAChain) {
  EXPECT_EQ(RunWithFinals(FinalBits(
                "logic [3:0] a, b, c, output bit [5:0] o, p",
                "$bits(b), $bits(c), $bits(p)",
                "  logic [3:0] x = 0; bit [5:0] y, z;\n", "x, x, x, y, z")),
            "4 4 6\n");
}

TEST(CheckerFormalTypeInheritanceRun, ASignedTypeCarriesOver) {
  EXPECT_EQ(
      RunWithFinals(FinalBits("logic signed [3:0] a, b", "$bits(b), b < 0, b",
                              "  logic signed [3:0] x = -3;\n", "x, x")),
      "4 1 -3\n");
}

TEST(CheckerFormalTypeInheritanceRun, ATypedefAndAnEnumNameCarryOver) {
  EXPECT_EQ(
      RunWithFinals(FinalBits("w_t g, h, st_t e, f", "$bits(h), $bits(f), f",
                              "  w_t x = 0; st_t y = S2;\n", "x, x, y, y")),
      "7 3 2\n");
}

TEST(CheckerFormalTypeInheritanceRun, AnImplicitTypeCarriesOver) {
  EXPECT_EQ(
      RunWithFinals(FinalBits(
          "input [3:0] a, b, input signed c, d", "$bits(b), $bits(d), d < 0",
          "  logic [3:0] x = 0; logic signed y = 1;\n", "x, x, y, y")),
      "4 1 1\n");
}

TEST(CheckerFormalTypeInheritanceRun, AnUnpackedDimensionStaysWithItsFormal) {
  EXPECT_EQ(RunWithFinals(
                FinalBits("logic [1:0] u [3], v", "$bits(v), $bits(u), 0",
                          "  logic [1:0] x [3]; logic [1:0] y = 0;\n", "x, y")),
            "2 6 0\n");
}

TEST(CheckerFormalTypeInheritanceRun, ADefaultStaysWithItsFormal) {
  EXPECT_EQ(RunWithFinals(FinalBits("logic [4:0] k = 0, m", "$bits(m), m, k",
                                    "  logic [4:0] y = 5'd9;\n", ", y")),
            "5 9 0\n");
}

TEST(CheckerFormalTypeInheritanceRun, ABareFormalKeepsItsOwnDefault) {
  EXPECT_EQ(
      RunWithFinals(FinalBits("input logic in, en = 1'b1", "$bits(en), en, in",
                              "  logic x = 0;\n", "x, ")),
      "1 1 0\n");
}

const char* const kMemberTypes =
    "typedef struct packed {logic [3:0] f, g;} ps_t;\n"
    "typedef struct {int f; int g;} us_t;\n"
    "typedef union packed {logic [7:0] f; logic [7:0] g;} pu_t;\n";

std::string MemberStimulus(const std::string& type, const std::string& init) {
  return "  " + type + " s = " + init +
         ";\n"
         "  logic a = 1;\n"
         "  clocking cb @(posedge clk); input a; endclocking\n"
         "  initial begin #12 s.f = 0; a = 0; #10 s.f = 3; a = 1; end\n";
}

std::string MemberBody(const std::string& read) {
  return "    always_ff @(negedge clk) $display(\"r %0d\", " + read +
         ");\n"
         "    a1: assert property (@(negedge clk) " +
         read +
         ")\n"
         "      else $display(\"a1 %0t\", $time);\n";
}

const char* const kMemberExpected = "a1 20\nr 0\nr 3\n";

std::string FormalMemberRun(const std::string& type, const std::string& init,
                            bool in_top) {
  std::string chk = "checker chk(" + type + " sv, logic clk);\n" +
                    MemberBody("sv.f") + "endchecker\n";
  std::string inner = MemberStimulus(type, init) + "  chk uc(s, clk);\n";
  std::string clock =
      "  logic clk = 0;\n  always #5 clk = ~clk;\n  initial #28 $finish;\n";
  if (in_top) {
    return RunLines(kMemberTypes + chk + "module t;\n" + clock + inner +
                    "endmodule\n");
  }
  return RunLines(kMemberTypes + chk + "module m(input logic clk);\n" + inner +
                  "endmodule\nmodule t;\n" + clock +
                  "  m u1(clk);\nendmodule\n");
}

std::string ScopeMemberRun(const std::string& read, bool in_top) {
  std::string chk = "  checker c2(logic clk);\n" + MemberBody(read) +
                    "  endchecker\n  c2 uc(clk);\n";
  std::string inner = MemberStimulus("ps_t", "'{4'd3, 4'd5}") + chk;
  std::string clock =
      "  logic clk = 0;\n  always #5 clk = ~clk;\n  initial #28 $finish;\n";
  if (in_top) {
    return RunLines(std::string(kMemberTypes) + "module t;\n" + clock + inner +
                    "endmodule\n");
  }
  return RunLines(std::string(kMemberTypes) + "module m(input logic clk);\n" +
                  inner + "endmodule\nmodule t;\n" + clock +
                  "  m u1(clk);\nendmodule\n");
}

TEST(CheckerMemberSelectRun, DISABLED_APackedStructFormalInTheTop) {
  EXPECT_EQ(FormalMemberRun("ps_t", "'{4'd3, 4'd5}", true), kMemberExpected);
}

TEST(CheckerMemberSelectRun, DISABLED_APackedStructFormalBelowTheTop) {
  EXPECT_EQ(FormalMemberRun("ps_t", "'{4'd3, 4'd5}", false), kMemberExpected);
}

TEST(CheckerMemberSelectRun, DISABLED_AnUnpackedStructFormal) {
  EXPECT_EQ(FormalMemberRun("us_t", "'{3, 5}", true), kMemberExpected);
  EXPECT_EQ(FormalMemberRun("us_t", "'{3, 5}", false), kMemberExpected);
}

TEST(CheckerMemberSelectRun, DISABLED_APackedUnionFormal) {
  EXPECT_EQ(FormalMemberRun("pu_t", "8'd3", true), kMemberExpected);
  EXPECT_EQ(FormalMemberRun("pu_t", "8'd3", false), kMemberExpected);
}

TEST(CheckerMemberSelectRun, TheDeclaringModulesStructInTheTop) {
  EXPECT_EQ(ScopeMemberRun("s.f", true), kMemberExpected);
}

TEST(CheckerMemberSelectRun, DISABLED_TheDeclaringModulesStructBelowTheTop) {
  EXPECT_EQ(ScopeMemberRun("s.f", false), kMemberExpected);
}

TEST(CheckerMemberSelectRun, TheDeclaringModulesClockingBlockInTheTop) {
  EXPECT_EQ(ScopeMemberRun("cb.a", true), "a1 20\nr 0\nr 1\n");
}

TEST(CheckerMemberSelectRun,
     DISABLED_TheDeclaringModulesClockingBlockBelowTheTop) {
  EXPECT_EQ(ScopeMemberRun("cb.a", false), "a1 20\nr 0\nr 1\n");
}

}  // namespace
