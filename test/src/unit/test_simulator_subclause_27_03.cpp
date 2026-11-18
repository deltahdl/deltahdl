#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(GenerateSchemeConstantSim, AnInterfaceParameterDrivesEverySchemeKind) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc;\n"
                       "  parameter int P = 1;\n"
                       "  if (P) begin : g initial $display(\"ia\"); end\n"
                       "  case (P)\n"
                       "    1: begin : h initial $display(\"ib\"); end\n"
                       "    default: ;\n"
                       "  endcase\n"
                       "  for (genvar k = 0; k < P + 1; k++) begin : l\n"
                       "    initial $display(\"ic%0d\", k);\n"
                       "  end\n"
                       "endinterface\n"
                       "module top; ifc i(); endmodule\n",
                       f),
            "ia\nib\nic0\nic1\n");
}

TEST(GenerateSchemeConstantSim,
     DISABLED_ABlockLocalparamSelectsANestedIfAndElseIf) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  if (1) begin : g\n"
                 "    localparam int W = 3;\n"
                 "    if (W == 3) begin : h initial $display(\"if\"); end\n"
                 "    else begin : h2 initial $display(\"no\"); end\n"
                 "    if (W == 9) begin : h3 initial $display(\"no\"); end\n"
                 "    else if (W == 3) begin : h4\n"
                 "      initial #1 $display(\"elseif\");\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "if\nelseif\n");
}

TEST(GenerateSchemeConstantSim,
     DISABLED_ACaseBlockLocalparamSelectsANestedSelectorAndItem) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  case (1)\n"
                 "    1: begin : g\n"
                 "      localparam int W = 3;\n"
                 "      case (W)\n"
                 "        3: begin : c initial $display(\"sel\"); end\n"
                 "        default: begin : d initial $display(\"no\"); end\n"
                 "      endcase\n"
                 "      case (1)\n"
                 "        (W == 4): begin : e initial $display(\"no\"); end\n"
                 "        (W == 3): begin : i\n"
                 "          initial #1 $display(\"item\");\n"
                 "        end\n"
                 "      endcase\n"
                 "    end\n"
                 "  endcase\n"
                 "endmodule\n",
                 f),
      "sel\nitem\n");
}

TEST(GenerateSchemeConstantSim,
     DISABLED_ALoopBlockLocalparamBoundsANestedLoop) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  for (genvar i = 0; i < 1; i++) begin : g\n"
                 "    localparam int W = 7;\n"
                 "    for (genvar j = W - 6; j < W; j += W - 4) begin : l\n"
                 "      initial #j $display(\"j%0d\", j);\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "j1\nj4\n");
}

TEST(GenerateSchemeConstantSim,
     DISABLED_ALocalparamFromTheGenvarSelectsPerIteration) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "module m;\n"
                "  for (genvar i = 0; i < 3; i++) begin : f\n"
                "    localparam int Q = i + 1;\n"
                "    if (Q == 2) begin : x initial $display(\"q%0d\", i); end\n"
                "  end\n"
                "endmodule\n",
                f),
            "q1\n");
}

TEST(GenerateSchemeConstantSim,
     DISABLED_ABlockParameterAndAnUntypedLocalparamSelect) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  if (1) begin : g\n"
                 "    parameter int PW = 2;\n"
                 "    localparam UW = 4;\n"
                 "    if (PW == 2) begin : p initial $display(\"param\"); end\n"
                 "    if (UW == 4) begin : u\n"
                 "      initial #1 $display(\"untyped\");\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "param\nuntyped\n");
}

TEST(GenerateSchemeConstantSim,
     DISABLED_ABlockLocalparamHidesAModuleParameterOfItsName) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  parameter int S = 1;\n"
                 "  if (1) begin : s\n"
                 "    localparam int S = 5;\n"
                 "    if (S == 5) begin : t initial $display(\"block\"); end\n"
                 "    else begin : u initial $display(\"module\"); end\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "block\n");
}

TEST(GenerateSchemeConstantSim,
     DISABLED_AnOuterBlockLocalparamReachesTwoBlocksBelow) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  if (1) begin : g\n"
                       "    localparam int W = 3;\n"
                       "    case (1)\n"
                       "      1: begin : k\n"
                       "        for (genvar n = 0; n < 1; n++) begin : l\n"
                       "          if (W == 3) begin : e\n"
                       "            initial $display(\"deep\");\n"
                       "          end\n"
                       "        end\n"
                       "      end\n"
                       "    endcase\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "deep\n");
}

TEST(GenerateSchemeConstantSim,
     DISABLED_InterfaceAndProgramBlockLocalparamsSelect) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "interface ifc;\n"
          "  if (1) begin : g\n"
          "    localparam int W = 2;\n"
          "    if (W == 2) begin : h initial $display(\"i\"); end\n"
          "  end\n"
          "endinterface\n"
          "program pr;\n"
          "  for (genvar i = 0; i < 1; i++) begin : g\n"
          "    localparam int W = 4;\n"
          "    case (W) 4: begin : h initial $display(\"p\"); end endcase\n"
          "  end\n"
          "endprogram\n"
          "module top; ifc u(); pr v(); endmodule\n",
          f),
      "i\np\n");
}

TEST(ConditionalGenerateSelectionSim, OnlyTheFirstOfTwoMatchingItemsIsBuilt) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  case (2)\n"
                       "    1, 2: begin : a initial $display(\"a\"); end\n"
                       "    2: begin : b initial $display(\"b\"); end\n"
                       "    default: begin : d initial $display(\"d\"); end\n"
                       "  endcase\n"
                       "endmodule\n",
                       f),
            "a\n");
}

TEST(ConditionalGenerateSelectionSim, AnInterfaceBuildsOnlyItsSelectedBlocks) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("interface ifc #(parameter int P = 3);\n"
                 "  case (P)\n"
                 "    1: begin : c1 initial $display(\"i1\"); end\n"
                 "    default: begin : cd initial $display(\"id\"); end\n"
                 "  endcase\n"
                 "  if (P == 3) begin : t initial #1 $display(\"it\"); end\n"
                 "  else begin : e initial #1 $display(\"ie\"); end\n"
                 "endinterface\n"
                 "module top; ifc i(); endmodule\n",
                 f),
      "id\nit\n");
}

TEST(ConditionalGenerateSelectionSim, AProgramBuildsOnlyItsSelectedBlocks) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program pr #(parameter int P = 0);\n"
                       "  if (P) begin : t initial $display(\"pt\"); end\n"
                       "  else begin : e initial $display(\"pe\"); end\n"
                       "  case (P)\n"
                       "    0: begin : c0 final $display(\"no\"); end\n"
                       "    1: begin : c1 initial $display(\"pc1\"); end\n"
                       "  endcase\n"
                       "endprogram\n"
                       "module top; pr p(); endmodule\n",
                       f),
            "pe\n");
}

TEST(ConditionalGenerateSelectionSim, ACheckerBuildsOnlyItsSelectedBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("checker ck(logic clk);\n"
                       "  if (0) begin : t\n"
                       "    a1: assert property (@(posedge clk) 0)\n"
                       "      else $display(\"ct\");\n"
                       "  end else begin : e\n"
                       "    a2: assert property (@(posedge clk) 0)\n"
                       "      else $display(\"ce\");\n"
                       "  end\n"
                       "endchecker\n"
                       "module top;\n"
                       "  logic clk = 0;\n"
                       "  ck c(clk);\n"
                       "  initial begin #1 clk = 1; #1 clk = 0; end\n"
                       "endmodule\n",
                       f),
            "ce\n");
}

TEST(ConditionalGenerateSelectionSim, NestedAlternativesPickOneGateOrNone) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module sel #(parameter int p = 0, q = 0)\n"
                 "    (input a, b, output y);\n"
                 "  if (p == 1)\n"
                 "    if (q == 0) begin : u and g(y, a, b); end\n"
                 "    else if (q == 2) begin : u or g(y, a, b); end\n"
                 "    else ;\n"
                 "  else if (p == 2)\n"
                 "    case (q)\n"
                 "      0, 1, 2: begin : u xor g(y, a, b); end\n"
                 "      default: begin : u xnor g(y, a, b); end\n"
                 "    endcase\n"
                 "endmodule\n"
                 "module top;\n"
                 "  logic a = 1, b = 0;\n"
                 "  wire y0, y1, y2, y3, y4, y5;\n"
                 "  sel #(1, 0) c0(a, b, y0);\n"
                 "  sel #(1, 2) c1(a, b, y1);\n"
                 "  sel #(1, 5) c2(a, b, y2);\n"
                 "  sel #(0, 0) c3(a, b, y3);\n"
                 "  sel #(2, 1) c4(a, b, y4);\n"
                 "  sel #(2, 7) c5(a, b, y5);\n"
                 "  initial begin\n"
                 "    #1 $display(\"%b%b%b%b%b%b\", y0, y1, y2, y3, y4, y5);\n"
                 "    b = 1;\n"
                 "    #1 $display(\"%b%b%b%b%b%b\", y0, y1, y2, y3, y4, y5);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "01zz10\n11zz01\n");
}

TEST(GenerateBlockEnumConstantsSim, EachBlockAndIterationFoldsItsOwnValues) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  if (1) begin : g1\n"
                       "    typedef enum {A, B} e_t;\n"
                       "    localparam int P = B;\n"
                       "  end\n"
                       "  if (1) begin : g2\n"
                       "    typedef enum {B, A} e_t;\n"
                       "    localparam int P = B;\n"
                       "  end\n"
                       "  for (genvar i = 0; i < 3; i++) begin : l\n"
                       "    typedef enum {X = i, Y} h_t;\n"
                       "    localparam int P = Y;\n"
                       "  end\n"
                       "  initial $display(\"%0d %0d %0d %0d %0d %0d\", g1.P,"
                       " g2.P, l[0].P, l[2].P, g1.B, g2.A);\n"
                       "endmodule\n",
                       f),
            "1 0 1 3 1 1\n");
}

TEST(GenerateBlockEnumConstantsSim, AHierarchicalNameReadsTheBlocksValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  if (1) begin : g1\n"
                       "    localparam int Z = 4;\n"
                       "    typedef enum {A = 5, B} e_t;\n"
                       "  end\n"
                       "  typedef enum {C = 7, D} f_t;\n"
                       "  initial $display(\"%0d %0d %0d %0d\", g1.Z, g1.A,"
                       " g1.B, D);\n"
                       "endmodule\n",
                       f),
            "4 5 6 8\n");
}

TEST(GenerateBlockEnumConstantsSim, ABlockVariableInitializerReadsBlockNames) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  if (1) begin : g1\n"
                 "    int a = 3;\n"
                 "    int b = a;\n"
                 "    typedef enum {A = 5, B} e_t;\n"
                 "    e_t v = B;\n"
                 "    int w = B;\n"
                 "    initial $display(\"%0d %0d %0d %0d\", b, v, w, B);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "3 6 6 6\n");
}

}  // namespace
