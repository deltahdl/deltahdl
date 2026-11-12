#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr const char* kInstrTrace =
    "0 0 30\n0 0 30\n100 0 30\n7 0 30\n7 0 30\n7 0 60\n";

std::string RunInstrExample(const char* case_statement) {
  SimFixture f;
  return RunCapture(
      std::string("module t;\n"
                  "  typedef union tagged {\n"
                  "    struct {\n"
                  "      bit [4:0] reg1, reg2, regd;\n"
                  "    } Add;\n"
                  "    union tagged {\n"
                  "      bit [9:0] JmpU;\n"
                  "      struct {\n"
                  "        bit [1:0] cc;\n"
                  "        bit [9:0] addr;\n"
                  "      } JmpC;\n"
                  "    } Jmp;\n"
                  "  } Instr;\n"
                  "  Instr instr;\n"
                  "  int rf [0:31];\n"
                  "  bit [9:0] pc;\n"
                  "  task automatic exec;\n") +
          case_statement +
          "    $display(\"%0d %0d %0d\", pc, rf[0], rf[3]);\n"
          "  endtask\n"
          "  initial begin\n"
          "    for (int k = 0; k < 32; k++) rf[k] = k * 10;\n"
          "    pc = 0;\n"
          "    instr = tagged Add '{5'd1, 5'd2, 5'd3}; exec;\n"
          "    instr = tagged Add '{5'd1, 5'd2, 5'd0}; exec;\n"
          "    instr = tagged Jmp (tagged JmpU 10'd100); exec;\n"
          "    instr = tagged Jmp (tagged JmpC '{2'd1, 10'd7}); exec;\n"
          "    instr = tagged Jmp (tagged JmpC '{2'd0, 10'd9}); exec;\n"
          "    instr = tagged Add '{5'd3, 5'd3, 5'd3}; exec;\n"
          "  end\n"
          "endmodule\n",
      f);
}

TEST(CaseMatchesExampleSim, TheValidIntExampleBindsTheValueOfTheValidTag) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef union tagged {\n"
                 "    void Invalid;\n"
                 "    int Valid;\n"
                 "  } VInt;\n"
                 "  VInt v;\n"
                 "  task show;\n"
                 "    case (v) matches\n"
                 "      tagged Invalid  : $display (\"v is Invalid\");\n"
                 "      tagged Valid .n : $display (\"v is Valid with value "
                 "%0d\", n);\n"
                 "    endcase\n"
                 "  endtask\n"
                 "  initial begin\n"
                 "    v = tagged Invalid; show;\n"
                 "    v = tagged Valid 42; show;\n"
                 "    v = tagged Valid -3; show;\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "v is Invalid\nv is Valid with value 42\nv is Valid with value -3\n");
}

TEST(CaseMatchesExampleSim, TheInstructionExampleFiltersAndNestsACase) {
  EXPECT_EQ(
      RunInstrExample(
          "    case (instr) matches\n"
          "      tagged Add '{.r1, .r2, .rd} &&& (rd != 0) : rf[rd] = rf[r1] + "
          "rf[r2];\n"
          "      tagged Jmp .j : case (j) matches\n"
          "                        tagged JmpU .a       : pc = pc + a;\n"
          "                        tagged JmpC '{.c, .a}: if (rf[c]) pc = a;\n"
          "                      endcase\n"
          "    endcase\n"),
      kInstrTrace);
}

TEST(CaseMatchesExampleSim, TheWildcardExampleSelectsTheNoOpForRegisterZero) {
  EXPECT_EQ(
      RunInstrExample(
          "    case (instr) matches\n"
          "      tagged Add '{.*, .*, 0}    : ;\n"
          "      tagged Add '{.r1, .r2, .rd}  : rf[rd] = rf[r1] + rf[r2];\n"
          "      tagged Jmp .j : case (j) matches\n"
          "                        tagged JmpU .a        : pc = pc + a;\n"
          "                        tagged JmpC '{.c, .a} : if (rf[c]) pc = "
          "a;\n"
          "                      endcase\n"
          "    endcase\n"),
      kInstrTrace);
}

TEST(CaseMatchesExampleSim, TheStructureExampleMatchesTheBoundStructure) {
  EXPECT_EQ(
      RunInstrExample("    case (instr) matches\n"
                      "      tagged Add .s: case (s) matches\n"
                      "                       '{.*, .*, 0}    : ;\n"
                      "                       '{.r1, .r2, .rd}  : rf[rd] = "
                      "rf[r1] + rf[r2];\n"
                      "                     endcase\n"
                      "      tagged Jmp .j: case (j) matches\n"
                      "                       tagged JmpU .a        : pc = pc "
                      "+ a;\n"
                      "                       tagged JmpC '{.c, .a} : if "
                      "(rf[c]) pc = a;\n"
                      "                     endcase\n"
                      "    endcase\n"),
      kInstrTrace);
}

TEST(CaseMatchesExampleSim, TheNestedTaggedExampleMatchesBothTags) {
  EXPECT_EQ(
      RunInstrExample(
          "    case (instr) matches\n"
          "      tagged Add '{.r1, .r2, .rd} &&& (rd != 0) : rf[rd] = rf[r1] + "
          "rf[r2];\n"
          "      tagged Jmp (tagged JmpU .a)                : pc = pc + a;\n"
          "      tagged Jmp (tagged JmpC '{.c, .a})         : if (rf[c]) pc = "
          "a;\n"
          "    endcase\n"),
      kInstrTrace);
}

TEST(CaseMatchesExampleSim, TheNamedMemberExampleMatchesInAnyOrder) {
  EXPECT_EQ(
      RunInstrExample(
          "    case (instr) matches\n"
          "      tagged Add '{reg2:.r2,regd:.rd,reg1:.r1} &&& (rd != 0):\n"
          "                                  rf[rd] = rf[r1] + rf[r2];\n"
          "      tagged Jmp (tagged JmpU .a)                : pc = pc + "
          "a;\n"
          "      tagged Jmp (tagged JmpC '{addr:.a,cc:.c}) : if (rf[c]) "
          "pc = a;\n"
          "    endcase\n"),
      kInstrTrace);
}

TEST(CaseMatchesItemSim, EveryFormOfCaseMatchesDecidesInEveryKindOfProcedure) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk;\n"
                       "  typedef union tagged {\n"
                       "    void Invalid;\n"
                       "    int Valid;\n"
                       "  } VInt;\n"
                       "  function automatic int f(VInt v);\n"
                       "    case (v) matches\n"
                       "      tagged Valid .n &&& (n > 0) : return n;\n"
                       "      default : return -1;\n"
                       "    endcase\n"
                       "  endfunction\n"
                       "endpackage\n"
                       "import pk::*;\n"
                       "function automatic int g(VInt v);\n"
                       "  casez (v) matches\n"
                       "    tagged Valid .n : return n + 100;\n"
                       "    tagged Invalid : return 0;\n"
                       "  endcase\n"
                       "endfunction\n"
                       "class C;\n"
                       "  function int m(VInt v);\n"
                       "    priority casex (v) matches\n"
                       "      tagged Valid .n : return n * 2;\n"
                       "      tagged Invalid : return 7;\n"
                       "    endcase\n"
                       "  endfunction\n"
                       "endclass\n"
                       "interface I;\n"
                       "  VInt v;\n"
                       "  initial begin\n"
                       "    v = tagged Valid 5;\n"
                       "    #2 unique case (v) matches\n"
                       "      tagged Invalid : $display(\"I invalid\");\n"
                       "      tagged Valid .n : $display(\"I %0d\", n);\n"
                       "    endcase\n"
                       "  end\n"
                       "endinterface\n"
                       "program p;\n"
                       "  VInt v;\n"
                       "  initial begin\n"
                       "    v = tagged Invalid;\n"
                       "    #3 case (v) matches\n"
                       "      tagged Valid .n : $display(\"P %0d\", n);\n"
                       "      default : $display(\"P default\");\n"
                       "    endcase\n"
                       "  end\n"
                       "endprogram\n"
                       "module t;\n"
                       "  I u();\n"
                       "  p pp();\n"
                       "  task tk(VInt v);\n"
                       "    case (v) matches\n"
                       "      tagged Valid .n : $display(\"T %0d\", n);\n"
                       "      tagged Invalid : $display(\"T invalid\");\n"
                       "    endcase\n"
                       "  endtask\n"
                       "  if (1) begin : gb\n"
                       "    VInt gv;\n"
                       "    initial begin\n"
                       "      gv = tagged Valid 9;\n"
                       "      #1 case (gv) matches\n"
                       "        tagged Invalid : $display(\"G invalid\");\n"
                       "        tagged Valid .n : $display(\"G %0d\", n);\n"
                       "      endcase\n"
                       "    end\n"
                       "  end\n"
                       "  initial begin\n"
                       "    C c;\n"
                       "    VInt a, b, z;\n"
                       "    c = new;\n"
                       "    a = tagged Valid 4;\n"
                       "    b = tagged Valid -2;\n"
                       "    z = tagged Invalid;\n"
                       "    $display(\"%0d %0d %0d %0d %0d %0d\", f(a), f(b), "
                       "f(z), g(a), c.m(a), c.m(z));\n"
                       "    tk(z);\n"
                       "    tk(a);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "4 -1 -1 104 8 7\nT invalid\nT 4\nG 9\nI 5\nP default\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

}  // namespace
