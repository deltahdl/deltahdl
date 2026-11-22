#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

using FsmRecognitionRun = VpiDesignRun;

TEST_F(FsmRecognitionRun, AnFsmIsNamedByItsStateSignal) {
  Run("module top;\n"
      "  parameter [1:0] /* tool enum fsm_e */ IDLE = 0, RUN = 1;\n"
      "  /* tool state_vector st enum fsm_e */\n"
      "  logic [1:0] st;\n"
      "  logic [1:0] /* tool enum fsm_e */ nx;\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiFsm, By("top")), std::vector<std::string>{"st"});
}

TEST_F(FsmRecognitionRun, APragmaFsmIsTheOnlyFsmOfASignalCodedAsOne) {
  Run("module top;\n"
      "  typedef enum logic [1:0] {X, Y, Z} t;\n"
      "  parameter [1:0] /* tool enum fsm_e */ IDLE = 0, RUN = 1;\n"
      "  /* tool state_vector st enum fsm_e */\n"
      "  t st = X;\n"
      "  logic clk = 0;\n"
      "  always @(posedge clk)\n"
      "    case (st)\n"
      "      X: st <= Y;\n"
      "      Y: st <= Z;\n"
      "      default: st <= X;\n"
      "    endcase\n"
      "  initial begin\n"
      "    #1 clk = 1; #1 clk = 0; #1 clk = 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(NamesOf(vpiFsm, By("top")), std::vector<std::string>{"st"});
  vpiHandle fsm = Named(vpiFsm, By("top"), "st");
  ASSERT_NE(fsm, nullptr);
  EXPECT_EQ(NamesOf(vpiFsmStates, fsm),
            (std::vector<std::string>{"IDLE", "RUN"}));
  EXPECT_EQ(vpi_get(vpiCoveredMax, fsm), 2);
}

TEST_F(FsmRecognitionRun, AnAscendingPartSelectReadsTheBitsItSelects) {
  Run("module top;\n"
      "  parameter [3:0] /* tool enum e */ A = 1, B = 4;\n"
      "  /* tool state_vector cur[0:3] f enum e */\n"
      "  logic [0:7] cur;\n"
      "  initial begin\n"
      "    cur = 8'b0001_0000; #1 cur = 8'b0100_0001;\n"
      "  end\n"
      "endmodule\n");
  vpiHandle fsm = Named(vpiFsm, By("top"), "f");
  ASSERT_NE(fsm, nullptr);
  vpiHandle select = vpi_handle(vpiFsmStateExpression, fsm);
  ASSERT_NE(select, nullptr);
  s_vpi_value left = {};
  left.format = vpiIntVal;
  vpi_get_value(vpi_handle(vpiLeftRange, select), &left);
  EXPECT_EQ(left.value.integer, 0);
  EXPECT_EQ(vpi_get(vpiCovered, Named(vpiFsmStates, fsm, "A")), 1);
  EXPECT_EQ(vpi_get(vpiCovered, Named(vpiFsmStates, fsm, "B")), 1);
  EXPECT_EQ(vpi_get(vpiCovered, fsm), 2);
}

TEST_F(FsmRecognitionRun, DISABLED_APartSelectOutsideTheSignalReachesNoState) {
  Run("module top;\n"
      "  parameter [1:0] /* tool enum e */ A = 0, B = 1;\n"
      "  /* tool state_vector cur[9:8] f enum e */\n"
      "  logic [7:0] cur;\n"
      "  initial begin\n"
      "    cur = 0; #1 cur = 1; #1 cur = 0;\n"
      "  end\n"
      "endmodule\n");
  vpiHandle fsm = Named(vpiFsm, By("top"), "f");
  ASSERT_NE(fsm, nullptr);
  EXPECT_EQ(vpi_get(vpiCovered, fsm), 0);
}

}  // namespace
}  // namespace delta
