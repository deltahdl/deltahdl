#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_parser.h"
#include "parser/ast_design.h"
#include "parser/ast_fsm.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

using Names = std::vector<std::string_view>;

const std::vector<FsmDecl>& FsmsOf(const ParseResult& result) {
  return result.cu->modules.front()->fsms;
}

TEST(FsmPragmaBinding, AStateVectorAndItsEnumParametersAreOneFsm) {
  auto r = Parse(
      "module top;\n"
      "  parameter [1:0] /* tool enum fsm_e */ IDLE = 0, RUN = 1, DONE = 2;\n"
      "  parameter OTHER = 3;\n"
      "  /* tool state_vector st enum fsm_e */\n"
      "  logic [1:0] st;\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(FsmsOf(r).size(), 1u);
  const FsmDecl& fsm = FsmsOf(r).front();
  EXPECT_EQ(fsm.state_signals, (Names{"st"}));
  EXPECT_FALSE(fsm.has_part_select);
  EXPECT_EQ(fsm.enum_name, "fsm_e");
  EXPECT_EQ(fsm.states, (Names{"IDLE", "RUN", "DONE"}));
}

TEST(FsmPragmaBinding, ASeparateEnumPragmaInTheDeclarationNamesTheEnum) {
  auto r = Parse(
      "module top;\n"
      "  parameter // tool enum my_fsm\n"
      "    S0 = 0, S1 = 1;\n"
      "  /* tool state_vector cs */\n"
      "  logic [1:0] /* tool enum my_fsm */ cs, ns, nonstate;\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(FsmsOf(r).size(), 1u);
  EXPECT_EQ(FsmsOf(r).front().state_signals, (Names{"cs"}));
  EXPECT_EQ(FsmsOf(r).front().enum_name, "my_fsm");
  EXPECT_EQ(FsmsOf(r).front().states, (Names{"S0", "S1"}));
}

TEST(FsmPragmaBinding, APartSelectStateKeepsItsBoundsAndName) {
  auto r = Parse(
      "module top;\n"
      "  parameter [1:0] /* tool enum sel_e */ A = 0, B = 3;\n"
      "  /* tool state_vector bus[5:4] sel_fsm enum sel_e */\n"
      "  logic [7:0] bus;\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(FsmsOf(r).size(), 1u);
  const FsmDecl& fsm = FsmsOf(r).front();
  EXPECT_EQ(fsm.state_signals, (Names{"bus"}));
  EXPECT_TRUE(fsm.has_part_select);
  EXPECT_EQ(fsm.msb, 5);
  EXPECT_EQ(fsm.lsb, 4);
  EXPECT_EQ(fsm.fsm_name, "sel_fsm");
  EXPECT_EQ(fsm.states, (Names{"A", "B"}));
}

TEST(FsmPragmaBinding, AConcatenationStateIsEverySignalItLists) {
  auto r = Parse(
      "module top;\n"
      "  parameter [1:0] /* tool enum cat_e */ A = 0, B = 1;\n"
      "  /* tool state_vector {hi, lo} cat_fsm enum cat_e */\n"
      "  logic hi, lo;\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(FsmsOf(r).size(), 1u);
  EXPECT_EQ(FsmsOf(r).front().state_signals, (Names{"hi", "lo"}));
  EXPECT_EQ(FsmsOf(r).front().fsm_name, "cat_fsm");
}

TEST(FsmPragmaBinding, EachModuleHoldsTheFsmsWrittenInIt) {
  auto r = Parse(
      "module a;\n"
      "  /* tool state_vector sa enum ea */\n"
      "  logic sa;\n"
      "endmodule\n"
      "module b;\n"
      "  /* tool state_vector sb enum eb */\n"
      "  logic sb;\n"
      "endmodule\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  ASSERT_EQ(r.cu->modules[0]->fsms.size(), 1u);
  ASSERT_EQ(r.cu->modules[1]->fsms.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->fsms.front().state_signals, (Names{"sa"}));
  EXPECT_EQ(r.cu->modules[1]->fsms.front().state_signals, (Names{"sb"}));
}

std::string Described(const std::vector<FsmDecl>& fsms) {
  std::string out;
  for (const FsmDecl& fsm : fsms) {
    if (!out.empty()) out += " | ";
    for (std::size_t i = 0; i < fsm.state_signals.size(); ++i) {
      if (i > 0) out += ',';
      out += fsm.state_signals[i];
    }
    if (fsm.has_part_select) {
      out +=
          "[" + std::to_string(fsm.msb) + ":" + std::to_string(fsm.lsb) + "]";
    }
    out += "/";
    out += fsm.fsm_name;
    out += "/";
    out += fsm.enum_name;
    out += "/";
    for (std::size_t i = 0; i < fsm.states.size(); ++i) {
      if (i > 0) out += ',';
      out += fsm.states[i];
    }
  }
  return out;
}

std::string FsmsWritten(const std::string& src) {
  auto r = Parse(src);
  EXPECT_FALSE(r.has_errors);
  if (r.cu->modules.empty()) return "no module";
  return Described(FsmsOf(r));
}

TEST(FsmPragmaBinding, TheFigureFortyTwoModuleIsOneFsmOfThreeStates) {
  EXPECT_EQ(FsmsWritten("module m3;\n"
                        "  reg [31:0] cs;\n"
                        "  reg [31:0] /* tool enum MY_FSM */ ns;\n"
                        "  reg [31:0] clk;\n"
                        "  reg [31:0] rst;\n"
                        "  // tool state_vector cs enum MY_FSM\n"
                        "  parameter // tool enum MY_FSM\n"
                        "    p1 = 10,\n"
                        "    p2 = 11,\n"
                        "    p3 = 12;\n"
                        "endmodule // m3\n"),
            "cs//MY_FSM/p1,p2,p3");
}

TEST(FsmPragmaBinding,
     DISABLED_AStatePragmaBeforeTheParameterWidthNamesNoStates) {
  EXPECT_EQ(FsmsWritten("module top;\n"
                        "  parameter /* tool enum e */ [1:0] S0 = 0, S1 = 1;\n"
                        "  /* tool state_vector st enum e */\n"
                        "  logic [1:0] st;\n"
                        "endmodule\n"),
            "st//e/");
}

TEST(FsmPragmaBinding, ALocalParameterDeclarationNamesStatesAsAParameterDoes) {
  EXPECT_EQ(FsmsWritten("module top;\n"
                        "  localparam [1:0] /* tool enum e */ S0 = 0, S1 = 1;\n"
                        "  localparam /* tool enum e */ S2 = 2;\n"
                        "  /* tool state_vector st enum e */\n"
                        "  logic [1:0] st;\n"
                        "endmodule\n"),
            "st//e/S0,S1,S2");
}

TEST(FsmPragmaBinding, DISABLED_AParameterPortDeclarationNamesStates) {
  EXPECT_EQ(FsmsWritten("module top #(parameter [1:0] /* tool enum e */ S0 = 0,"
                        " S1 = 1);\n"
                        "  /* tool state_vector st enum e */\n"
                        "  logic [1:0] st;\n"
                        "endmodule\n"),
            "st//e/S0,S1");
}

TEST(FsmPragmaBinding, AnAscendingPartSelectKeepsItsBounds) {
  EXPECT_EQ(FsmsWritten("module top;\n"
                        "  parameter [3:0] /* tool enum e */ A = 0, B = 1;\n"
                        "  /* tool state_vector cur[0:3] f enum e */\n"
                        "  logic [0:7] cur;\n"
                        "endmodule\n"),
            "cur[0:3]/f/e/A,B");
}

TEST(FsmPragmaBinding, AnFsmNameMayBeTheEnumerationName) {
  EXPECT_EQ(FsmsWritten("module top;\n"
                        "  parameter [3:0] /* tool enum st_e */ A = 0, B = 1;\n"
                        "  /* tool state_vector cs[3:0] st_e enum st_e */\n"
                        "  logic [7:0] cs;\n"
                        "endmodule\n"),
            "cs[3:0]/st_e/st_e/A,B");
}

TEST(FsmPragmaBinding, ASeparatePragmaBindsOnARegAndANetDeclaration) {
  EXPECT_EQ(FsmsWritten("module top;\n"
                        "  parameter /* tool enum e */ A = 0, B = 1;\n"
                        "  parameter /* tool enum f */ C = 0;\n"
                        "  /* tool state_vector cs */\n"
                        "  reg [1:0] /* tool enum e */ cs;\n"
                        "  /* tool state_vector ws */\n"
                        "  wire [1:0] /* tool enum f */ ws;\n"
                        "endmodule\n"),
            "cs//e/A,B | ws//f/C");
}

TEST(FsmPragmaBinding, ASeparatePragmaWithoutToolBindsNothing) {
  EXPECT_EQ(FsmsWritten("module top;\n"
                        "  parameter /* tool enum e */ A = 0, B = 1;\n"
                        "  /* tool state_vector cs */\n"
                        "  logic [1:0] /* enum e */ cs;\n"
                        "endmodule\n"),
            "");
}

TEST(FsmPragmaBinding,
     DISABLED_ASeparatePragmaBeforeTheRangeOrAfterTheNameBindsNothing) {
  EXPECT_EQ(FsmsWritten("module top;\n"
                        "  parameter /* tool enum e */ A = 0, B = 1;\n"
                        "  /* tool state_vector cs */\n"
                        "  logic /* tool enum e */ [1:0] cs;\n"
                        "  /* tool state_vector ds */\n"
                        "  logic [1:0] ds /* tool enum e */;\n"
                        "endmodule\n"),
            "");
}

TEST(FsmPragmaBinding, ASeparatePragmaAfterTheTypeOfARangelessSignalBinds) {
  EXPECT_EQ(FsmsWritten("module top;\n"
                        "  parameter /* tool enum e */ A = 0, B = 1;\n"
                        "  /* tool state_vector cs */\n"
                        "  logic /* tool enum e */ cs;\n"
                        "endmodule\n"),
            "cs//e/A,B");
}

TEST(FsmPragmaBinding, AStateVectorWithNoEnumerationIsNoFsm) {
  EXPECT_EQ(FsmsWritten("module top;\n"
                        "  parameter /* tool enum my_fsm */ A = 0, B = 1;\n"
                        "  /* tool state_vector st */\n"
                        "  logic [1:0] st;\n"
                        "  /* tool state_vector cs */\n"
                        "  logic [1:0] cs;\n"
                        "  logic [1:0] /* tool enum my_fsm */ other;\n"
                        "endmodule\n"),
            "");
}

TEST(FsmPragmaBinding, DISABLED_AStateVectorInTheCompilationUnitIsNoFsm) {
  EXPECT_EQ(FsmsWritten("/* tool state_vector st enum e */\n"
                        "module top;\n"
                        "  parameter /* tool enum e */ A = 0, B = 1;\n"
                        "  logic [1:0] st;\n"
                        "endmodule\n"
                        "// tool state_vector st enum e\n"),
            "");
}

TEST(FsmPragmaBinding,
     DISABLED_AStateVectorAfterItsSignalInAGenerateBlockBinds) {
  EXPECT_EQ(FsmsWritten("module top;\n"
                        "  parameter /* tool enum e */ A = 0, B = 1;\n"
                        "  if (1) begin : g\n"
                        "    logic [1:0] /* tool enum e */ st;\n"
                        "    /* tool state_vector st */\n"
                        "  end\n"
                        "endmodule\n"),
            "st//e/A,B");
}

TEST(FsmPragmaBinding,
     DISABLED_AnInterfaceAndAProgramHoldTheFsmsWrittenInThem) {
  auto r = Parse(
      "interface bus_if;\n"
      "  parameter /* tool enum ie */ I0 = 0, I1 = 1;\n"
      "  logic [1:0] /* tool enum ie */ ist;\n"
      "  /* tool state_vector ist */\n"
      "endinterface\n"
      "program prg;\n"
      "  parameter /* tool enum pe */ P0 = 0;\n"
      "  // tool state_vector pst enum pe\n"
      "  logic [1:0] pst;\n"
      "endprogram\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(Described(r.cu->interfaces.front()->fsms), "ist//ie/I0,I1");
  EXPECT_EQ(Described(r.cu->programs.front()->fsms), "pst//pe/P0");
}

}  // namespace
