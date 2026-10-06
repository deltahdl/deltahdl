#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_parser.h"
#include "parser/ast_design.h"
#include "parser/ast_fsm.h"
#include "parser/ast_module.h"

using namespace delta;

// §40.4: an FSM is identified by its state register or expression, its
// optional next-state register and its legal states, each named by a pragma
// the lexer recognizes in a comment. The parser gives each module the FSMs its
// pragmas identify: the signal or signals holding the current state, the
// enumeration name tying the pragmas of one FSM together, and the parameters
// that name its legal states.

namespace {

using Names = std::vector<std::string_view>;

// The FSMs the only module of `src` was given.
const std::vector<FsmDecl>& FsmsOf(const ParseResult& result) {
  return result.cu->modules.front()->fsms;
}

// §40.4.1 and §40.4.6: a state_vector pragma naming its signal and its
// enumeration, and the parameters a declaration tagged with that enumeration
// declares, are one FSM whose legal states are those parameters, and only
// those: a parameter declared by another declaration is none of them.
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

// §40.4.1 with §40.4.5 and §40.4.7: a state_vector pragma that names no
// enumeration takes the one a separate pragma gives right after the bit range
// of the signal's declaration, the first signal declared there holding the
// current state; a pragma in a one-line comment counts as one in a block
// comment.
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

// §40.4.2: a part-select holding the current state keeps its bounds and the
// FSM name the pragma gives it.
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

// §40.4.3: a concatenation holding the current state is every signal it
// lists, in order.
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

// §40.4.1: a pragma belongs to the module definition it is written in, so
// each of two modules holds only its own FSM.
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
