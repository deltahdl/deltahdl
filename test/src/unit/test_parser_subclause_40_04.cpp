#include <gtest/gtest.h>

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

}  // namespace
