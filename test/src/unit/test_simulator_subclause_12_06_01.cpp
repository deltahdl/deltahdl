#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(CaseMatchesItemSim, CaseMatchesConstantMatch) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd2;\n"
                      "    case(sel) matches\n"
                      "      8'd1: x = 8'd10;\n"
                      "      8'd2: x = 8'd20;\n"
                      "      8'd3: x = 8'd30;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            20u);
}

TEST(CaseMatchesItemSim, CaseMatchesDefaultFallthrough) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd99;\n"
                      "    case(sel) matches\n"
                      "      8'd1: x = 8'd10;\n"
                      "      8'd2: x = 8'd20;\n"
                      "      default: x = 8'd77;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            77u);
}

TEST(CaseMatchesItemSim, CaseMatchesFirstMatchWins) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd1;\n"
                      "    case(sel) matches\n"
                      "      8'd1: x = 8'd10;\n"
                      "      8'd1: x = 8'd20;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            10u);
}

TEST(CaseMatchesItemSim, CaseMatchesGuardTrue) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  logic en;\n"
                      "  initial begin\n"
                      "    sel = 8'd5;\n"
                      "    en = 1'b1;\n"
                      "    case(sel) matches\n"
                      "      8'd5 &&& en: x = 8'd10;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            10u);
}

TEST(CaseMatchesItemSim, CaseMatchesGuardFalse) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  logic en;\n"
                      "  initial begin\n"
                      "    sel = 8'd5;\n"
                      "    en = 1'b0;\n"
                      "    case(sel) matches\n"
                      "      8'd5 &&& en: x = 8'd10;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            99u);
}

TEST(CaseMatchesItemSim, CaseMatchesGuardFalseSecondMatches) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd5;\n"
                      "    case(sel) matches\n"
                      "      8'd5 &&& 1'b0: x = 8'd10;\n"
                      "      8'd5: x = 8'd20;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            20u);
}

TEST(CaseMatchesItemSim, CasezMatchesWildcard) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [3:0] sel;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    sel = 4'b1010;\n"
                      "    casez(sel) matches\n"
                      "      4'b1???: x = 8'd1;\n"
                      "      4'b0???: x = 8'd2;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            1u);
}

TEST(CaseMatchesItemSim, PriorityCaseMatchesNoMatchViolation) {
  SimFixture f;
  RunModuleNoVar(f,
                 "module t;\n"
                 "  logic [7:0] sel, x;\n"
                 "  initial begin\n"
                 "    sel = 8'd99;\n"
                 "    x = 8'd0;\n"
                 "    priority case(sel) matches\n"
                 "      8'd1: x = 8'd10;\n"
                 "      8'd2: x = 8'd20;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseMatchesItemSim, PriorityCaseMatchesNoMatchWithDefaultNoViolation) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd99;\n"
                      "    priority case(sel) matches\n"
                      "      8'd1: x = 8'd10;\n"
                      "      8'd2: x = 8'd20;\n"
                      "      default: x = 8'd55;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            55u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(CaseMatchesItemSim, UniqueCaseMatchesOverlapViolation) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd1;\n"
                      "    unique case(sel) matches\n"
                      "      8'd1: x = 8'd10;\n"
                      "      8'd1: x = 8'd20;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            10u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseMatchesItemSim, CaseMatchesNoMatchNoDefault) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd99;\n"
                      "    x = 8'd42;\n"
                      "    case(sel) matches\n"
                      "      8'd1: x = 8'd10;\n"
                      "      8'd2: x = 8'd20;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            42u);
}

TEST(CaseMatchesItemSim, CaseMatchesWildcardPattern) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [3:0] sel;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    sel = 4'b1010;\n"
                      "    casez(sel) matches\n"
                      "      4'b0???: x = 8'd1;\n"
                      "      4'b1???: x = 8'd2;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            2u);
}

TEST(CaseMatchesItemSim, CaseMatchesWildcardNoMatch) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [3:0] sel;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    sel = 4'b1010;\n"
                      "    case(sel) matches\n"
                      "      4'b0??0: x = 8'd1;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            99u);
}

TEST(CaseMatchesItemSim, CasexMatchesXInSelectorDontCare) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [3:0] sel;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    sel = 4'bx010;\n"
                      "    casex(sel) matches\n"
                      "      4'b1010: x = 8'd1;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            1u);
}

TEST(CaseMatchesItemSim, CaseMatchesXInSelectorNoMatch) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [3:0] sel;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    sel = 4'bx010;\n"
                      "    case(sel) matches\n"
                      "      4'b1010: x = 8'd1;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            99u);
}

TEST(CaseMatchesItemSim, CaseMatchesSelectorEvaluatedExactlyOnce) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  int cnt;\n"
                      "  logic [7:0] x;\n"
                      "  function automatic logic [7:0] sel_fn();\n"
                      "    cnt = cnt + 1;\n"
                      "    return 8'd2;\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    cnt = 0;\n"
                      "    x = 8'd0;\n"
                      "    case (sel_fn()) matches\n"
                      "      8'd1: x = 8'd11;\n"
                      "      8'd2: x = 8'd22;\n"
                      "      8'd3: x = 8'd33;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "cnt"),
            1u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 22u);
}

TEST(CaseMatchesItemSim, CaseMatchesDefaultIgnoredDuringSearch) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd2;\n"
                      "    case(sel) matches\n"
                      "      default: x = 8'd99;\n"
                      "      8'd1: x = 8'd10;\n"
                      "      8'd2: x = 8'd20;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            20u);
}

TEST(CaseMatchesItemSim, CaseMatchesFirstOfOverlappingPatternsWins) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [3:0] sel;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    sel = 4'b1010;\n"
                      "    casez(sel) matches\n"
                      "      4'b1???: x = 8'd1;\n"
                      "      4'b1010: x = 8'd2;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            1u);
}

TEST(CaseMatchesItemSim, UniqueCaseMatchesNoMatchViolation) {
  SimFixture f;
  RunModuleNoVar(f,
                 "module t;\n"
                 "  logic [7:0] sel, x;\n"
                 "  initial begin\n"
                 "    sel = 8'd99;\n"
                 "    x = 8'd0;\n"
                 "    unique case(sel) matches\n"
                 "      8'd1: x = 8'd10;\n"
                 "      8'd2: x = 8'd20;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseMatchesItemSim, UniqueCaseMatchesNoMatchWithDefaultNoViolation) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd99;\n"
                      "    unique case(sel) matches\n"
                      "      8'd1: x = 8'd10;\n"
                      "      8'd2: x = 8'd20;\n"
                      "      default: x = 8'd77;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            77u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(CaseMatchesItemSim, CaseMatchesGuardUnknownNotSelected) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  logic en;\n"
                      "  initial begin\n"
                      "    sel = 8'd5;\n"
                      "    en = 1'bx;\n"
                      "    case(sel) matches\n"
                      "      8'd5 &&& en: x = 8'd10;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            99u);
}

TEST(CaseMatchesItemSim, CaseMatchesParameterPattern) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  parameter P = 8'd2;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd2;\n"
                      "    case(sel) matches\n"
                      "      P: x = 8'd20;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            20u);
}

TEST(CaseMatchesItemSim, CaseMatchesLocalparamPattern) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  localparam LP = 8'd7;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd7;\n"
                      "    case(sel) matches\n"
                      "      LP: x = 8'd70;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            70u);
}

TEST(CaseMatchesItemSim, CaseMatchesGuardMultibitNonzeroTrue) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  logic [3:0] fexpr;\n"
                      "  initial begin\n"
                      "    sel = 8'd5;\n"
                      "    fexpr = 4'd9;\n"
                      "    case(sel) matches\n"
                      "      8'd5 &&& fexpr: x = 8'd10;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            10u);
}

TEST(CaseMatchesItemSim, CasezMatchesZInSelectorIgnored) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [3:0] sel;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    sel = 4'bz010;\n"
                      "    casez(sel) matches\n"
                      "      4'b1010: x = 8'd1;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            1u);
}

TEST(CaseMatchesItemSim, CasexMatchesZInSelectorIgnored) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [3:0] sel;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    sel = 4'bz010;\n"
                      "    casex(sel) matches\n"
                      "      4'b1010: x = 8'd1;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            1u);
}

constexpr const char* kTaggedTypes =
    "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
    "  typedef union tagged { logic [3:0] A; logic [3:0] B; } U;\n";

std::string TaggedModule(const std::string& body) {
  return "module t;\n" + std::string(kTaggedTypes) + body + "endmodule\n";
}

TEST(CaseMatchesItemSim, AnIdentifierMemberPatternBindsTheMember) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      TaggedModule("  VInt v;\n"
                                   "  int y;\n"
                                   "  initial begin\n"
                                   "    v = tagged Valid (37);\n"
                                   "    case (v) matches\n"
                                   "      tagged Invalid : y = 1;\n"
                                   "      tagged Valid .n : y = n;\n"
                                   "    endcase\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            37u);
}

TEST(CaseMatchesItemSim, ATaggedPatternRejectsAValueOfAnotherTag) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      TaggedModule("  VInt v;\n"
                                   "  int y;\n"
                                   "  initial begin\n"
                                   "    v = tagged Invalid;\n"
                                   "    case (v) matches\n"
                                   "      tagged Valid .n : y = 1;\n"
                                   "      default : y = 2;\n"
                                   "    endcase\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            2u);
}

TEST(CaseMatchesItemSim, AWildcardMemberPatternMatchesItsTag) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      TaggedModule("  VInt v;\n"
                                   "  int y;\n"
                                   "  initial begin\n"
                                   "    v = tagged Valid (12);\n"
                                   "    case (v) matches\n"
                                   "      tagged Valid .* : y = 1;\n"
                                   "      default : y = 2;\n"
                                   "    endcase\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            1u);
}

TEST(CaseMatchesItemSim, AConstantMemberPatternComparesTheTagFirst) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      TaggedModule("  U u;\n"
                                   "  int y;\n"
                                   "  initial begin\n"
                                   "    u = tagged B (4'd6);\n"
                                   "    case (u) matches\n"
                                   "      tagged A 6 : y = 1;\n"
                                   "      tagged B 6 : y = 2;\n"
                                   "      default : y = 3;\n"
                                   "    endcase\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            2u);
}

TEST(CaseMatchesItemSim, CasezIgnoresAZBitOfTheMember) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      TaggedModule("  U u;\n"
                                   "  int y;\n"
                                   "  initial begin\n"
                                   "    u = tagged B (4'b1z01);\n"
                                   "    casez (u) matches\n"
                                   "      tagged B 4'b1101 : y = 1;\n"
                                   "      default : y = 2;\n"
                                   "    endcase\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            1u);
}

TEST(CaseMatchesItemSim, TheFilterReadsTheBoundIdentifier) {
  SimFixture f;
  auto* design =
      ElaborateSrc(TaggedModule("  U u;\n"
                                "  int y, z;\n"
                                "  initial begin\n"
                                "    u = tagged A (4'd3);\n"
                                "    case (u) matches\n"
                                "      tagged A .x &&& (x < 8) : y = x + 100;\n"
                                "      tagged A .x : y = 1;\n"
                                "    endcase\n"
                                "    u = tagged A (4'd9);\n"
                                "    case (u) matches\n"
                                "      tagged A .x &&& (x < 8) : z = x + 100;\n"
                                "      tagged A .x : z = 1;\n"
                                "    endcase\n"
                                "  end\n"),
                   f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindVariable("y");
  auto* z = f.ctx.FindVariable("z");
  ASSERT_NE(y, nullptr);
  ASSERT_NE(z, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 103u);
  EXPECT_EQ(z->value.ToUint64(), 1u);
}

std::string StructModule(const std::string& body) {
  return "module t;\n"
         "  typedef struct { bit [3:0] a; bit [3:0] b; } S;\n"
         "  typedef union tagged {\n"
         "    struct { bit [4:0] reg1, reg2, regd; } Add;\n"
         "    struct { bit [1:0] cc; bit [9:0] addr; } JmpC;\n"
         "  } Instr;\n" +
         body + "endmodule\n";
}

TEST(CaseMatchesItemSim, APositionalStructurePatternMatchesEachMember) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      StructModule("  S s;\n"
                                   "  int y;\n"
                                   "  initial begin\n"
                                   "    s = '{5, 9};\n"
                                   "    case (s) matches\n"
                                   "      '{9, 5} : y = 1;\n"
                                   "      '{5, 9} : y = 2;\n"
                                   "      default : y = 3;\n"
                                   "    endcase\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            2u);
}

TEST(CaseMatchesItemSim, AStructurePatternWildcardMatchesAnyMember) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      StructModule("  S s;\n"
                                   "  int y;\n"
                                   "  initial begin\n"
                                   "    s = '{5, 9};\n"
                                   "    case (s) matches\n"
                                   "      '{.*, 8} : y = 1;\n"
                                   "      '{.*, 9} : y = 2;\n"
                                   "      default : y = 3;\n"
                                   "    endcase\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            2u);
}

TEST(CaseMatchesItemSim, ANamedStructurePatternBindsAMember) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      StructModule("  S s;\n"
                                   "  int y;\n"
                                   "  initial begin\n"
                                   "    s = '{5, 9};\n"
                                   "    case (s) matches\n"
                                   "      '{b:5, a:.aa} : y = 1;\n"
                                   "      '{a:5, b:.bb} : y = bb + 100;\n"
                                   "      default : y = 3;\n"
                                   "    endcase\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            109u);
}

TEST(CaseMatchesItemSim, ANamedStructurePatternUnderATagBindsItsMembers) {
  SimFixture f;
  auto* design = ElaborateSrc(
      StructModule("  Instr instr;\n"
                   "  int y, z;\n"
                   "  initial begin\n"
                   "    instr = tagged Add '{1, 2, 6};\n"
                   "    case (instr) matches\n"
                   "      tagged Add '{reg2:.r2, regd:.rd, reg1:.r1} :\n"
                   "        y = r1 * 100 + r2 * 10 + rd;\n"
                   "      tagged JmpC '{addr:.a} : y = a;\n"
                   "    endcase\n"
                   "    instr = tagged JmpC '{2, 300};\n"
                   "    case (instr) matches\n"
                   "      tagged Add '{reg2:.r2, regd:.rd, reg1:.r1} :\n"
                   "        z = r1 * 100 + r2 * 10 + rd;\n"
                   "      tagged JmpC '{addr:.a} : z = a;\n"
                   "    endcase\n"
                   "  end\n"),
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindVariable("y");
  auto* z = f.ctx.FindVariable("z");
  ASSERT_NE(y, nullptr);
  ASSERT_NE(z, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 126u);
  EXPECT_EQ(z->value.ToUint64(), 300u);
}

TEST(CaseMatchesItemSim, AFunctionBodyBindsTheMatchedMember) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      TaggedModule("  VInt v;\n"
                                   "  int y;\n"
                                   "  function int f();\n"
                                   "    case (v) matches\n"
                                   "      tagged Invalid : return 1;\n"
                                   "      tagged Valid .n : return n;\n"
                                   "    endcase\n"
                                   "    return 2;\n"
                                   "  endfunction\n"
                                   "  initial begin\n"
                                   "    v = tagged Valid (37);\n"
                                   "    y = f();\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            37u);
}

TEST(CaseMatchesItemSim, PlainCaseConstantPatternComparesEveryBit) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] s = 4'b1000, t = 4'bx010;\n"
      "  int n = 0;\n"
      "  initial begin\n"
      "    case (s) matches 4'b1x00: n += 1; default: ; endcase\n"
      "    case (t) matches 4'bx010: n += 10; default: ; endcase\n"
      "  end\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 10u);
}

TEST(CaseMatchesItemSim, TaggedPatternAgainstAStructureMember) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  typedef struct { VInt u; int k; } S;\n"
      "  S s;\n"
      "  int y = 0;\n"
      "  initial begin\n"
      "    s.u = tagged Valid 5;\n"
      "    case (s.u) matches tagged Valid .n: y = n; default: y = -1; "
      "endcase\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 5u);
}

TEST(CaseMatchesItemSim, StructurePatternAgainstAStructureMember) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef struct { int a; int b; } P;\n"
      "  typedef struct { P p; int k; } S;\n"
      "  S s;\n"
      "  int r = 0;\n"
      "  initial begin\n"
      "    s.p = '{3, 4};\n"
      "    case (s.p) matches\n"
      "      '{a: .x, b: .z}: r = x * 10 + z;\n"
      "      default: r = -1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 34u);
}

TEST(CaseMatchesItemSim, TaggedPatternAgainstACallResult) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  function automatic VInt f(); return tagged Valid 4; endfunction\n"
      "  int y = 0;\n"
      "  initial case (f()) matches tagged Valid .n: y = n; default: y = -1; "
      "endcase\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 4u);
}

TEST(CaseMatchesItemSim, StructurePatternAgainstACallResult) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef struct { int a; int b; } P;\n"
      "  function automatic P g(); return '{7, 8}; endfunction\n"
      "  int r = 0;\n"
      "  initial case (g()) matches '{.x, .z}: r = x * 10 + z; default: r = "
      "-1; endcase\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 78u);
}

TEST(CaseMatchesItemSim, BoundTaggedUnionKeepsItsTag) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module t;\n"
      "  typedef union tagged { bit [9:0] JmpU; bit [3:0] JmpC; } J;\n"
      "  typedef union tagged { void Nop; J Jmp; } Instr;\n"
      "  Instr instr;\n"
      "  int y = 0;\n"
      "  initial begin\n"
      "    instr = tagged Jmp (tagged JmpU 10'd7);\n"
      "    case (instr) matches\n"
      "      tagged Jmp .j: case (j) matches\n"
      "                       tagged JmpU .a: y = a;\n"
      "                       default: y = -1;\n"
      "                     endcase\n"
      "      default: y = -2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 7u);
}

}  // namespace
