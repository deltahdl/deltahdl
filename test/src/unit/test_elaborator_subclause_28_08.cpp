#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(GateElaboration, TranEmitsZeroContinuousAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  tran (a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 0u);
}

TEST(GateElaboration, RtranEmitsZeroContinuousAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  rtran (a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 0u);
}

TEST(GateElaboration, Tranif0EmitsZeroContinuousAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, en;\n"
      "  tranif0 t1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 0u);
}

TEST(GateElaboration, Tranif1EmitsZeroContinuousAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, en;\n"
      "  tranif1 t1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 0u);
}

TEST(GateElaboration, Rtranif0EmitsZeroContinuousAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, en;\n"
      "  rtranif0 r1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 0u);
}

TEST(GateElaboration, Rtranif1EmitsZeroContinuousAssigns) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, en;\n"
      "  rtranif1 r1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->assigns.size(), 0u);
}

TEST(BidirectionalSwitchTerminals, RtranAcceptsScalarNets) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  rtran r1(a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BidirectionalSwitchTerminals, RtranAcceptsBitSelectOfVector) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire [3:0] vec;\n"
      "  wire b;\n"
      "  rtran r1(vec[2], b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BidirectionalSwitchTerminals, RtranRejectsWholeVector) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [3:0] vec;\n"
      "  wire b;\n"
      "  rtran r1(vec, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a resistive bidirectional pass switch terminal "
                            "connects to a single bit",
                            4, "28.8"));
}

TEST(BidirectionalSwitchTerminals, RtranRejectsPartSelect) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [3:0] vec;\n"
      "  wire b;\n"
      "  rtran r1(vec[1:0], b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a resistive bidirectional pass switch terminal "
                            "connects to a single bit",
                            4, "28.8"));
}

TEST(BidirectionalSwitchTerminals, Rtranif0RejectsWholeVector) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [3:0] vec;\n"
      "  wire b, en;\n"
      "  rtranif0 r1(vec, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a resistive bidirectional pass switch terminal "
                            "connects to a single bit",
                            4, "28.8"));
}

TEST(BidirectionalSwitchTerminals, Rtranif1RejectsPartSelect) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [7:0] vec;\n"
      "  wire b, en;\n"
      "  rtranif1 r1(b, vec[3:1], en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a resistive bidirectional pass switch terminal "
                            "connects to a single bit",
                            4, "28.8"));
}

TEST(BidirectionalSwitchTerminals, RtranRejectsUdnt) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net a, b;\n"
      "  rtran r1(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resistive bidirectional pass switch terminal "
                            "cannot connect to a user-defined net type",
                            4, "28.8"));
}

TEST(BidirectionalSwitchTerminals, Rtranif0RejectsUdnt) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net a, b;\n"
      "  wire en;\n"
      "  rtranif0 r1(a, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resistive bidirectional pass switch terminal "
                            "cannot connect to a user-defined net type",
                            5, "28.8"));
}

TEST(BidirectionalSwitchTerminals, Rtranif1RejectsUdnt) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net a, b;\n"
      "  wire en;\n"
      "  rtranif1 r1(a, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resistive bidirectional pass switch terminal "
                            "cannot connect to a user-defined net type",
                            5, "28.8"));
}

TEST(BidirectionalSwitchTerminals, TranRejectsWholeVector) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [3:0] a, b;\n"
      "  tran t1(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "primitive output or inout terminal must be a "
                            "1-bit net or structural net expression (got "
                            "width 4)",
                            3, "4.9.6"));
}

TEST(BidirectionalSwitchUdnt, TranAcceptsSameUdntOnBothSides) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net a, b;\n"
      "  tran t1(a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BidirectionalSwitchUdnt, TranRejectsUdntWithBuiltin) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net a;\n"
      "  wire b;\n"
      "  tran t1(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bidirectional pass switch cannot connect a "
                            "user-defined nettype to a built-in net",
                            5, "28.8"));
}

TEST(BidirectionalSwitchUdnt, TranRejectsDifferentUdnts) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic net_a;\n"
      "  nettype logic net_b;\n"
      "  net_a a;\n"
      "  net_b b;\n"
      "  tran t1(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bidirectional pass switch cannot connect "
                            "different user-defined nettypes ('net_a' and "
                            "'net_b')",
                            6, "28.8"));
}

TEST(BidirectionalSwitchUdnt, Tranif1RejectsUdntWithBuiltin) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net a;\n"
      "  wire b, en;\n"
      "  tranif1 t1(a, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bidirectional pass switch cannot connect a "
                            "user-defined nettype to a built-in net",
                            5, "28.8"));
}

TEST(BidirectionalSwitchUdnt, Tranif1AcceptsSameUdntOnBothSides) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net a, b;\n"
      "  wire en;\n"
      "  tranif1 t1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BidirectionalSwitchControlType, Tranif1AcceptsWireControl) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, en;\n"
      "  tranif1 t1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BidirectionalSwitchControlType, Tranif1AcceptsLogicVariableControl) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  logic en;\n"
      "  tranif1 t1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BidirectionalSwitchControlType, Tranif0AcceptsBitVariableControl) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  bit en;\n"
      "  tranif0 t1(a, b, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BidirectionalSwitchControlType, Tranif1RejectsRealControl) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  real en;\n"
      "  tranif1 t1(a, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "control input of pass-enable switch cannot be of "
                            "type 'real'",
                            4, "28.8"));
}

TEST(BidirectionalSwitchControlType, Rtranif0RejectsStringControl) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  string en;\n"
      "  rtranif0 r1(a, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "control input of pass-enable switch cannot be of "
                            "type 'string'",
                            4, "28.8"));
}

TEST(BidirectionalSwitchControlType, Tranif0RejectsChandleControl) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  chandle en;\n"
      "  tranif0 t1(a, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "control input of pass-enable switch cannot be of "
                            "type 'chandle'",
                            4, "28.8"));
}

TEST(BidirectionalSwitchControlType, Rtranif1RejectsEventControl) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b;\n"
      "  event en;\n"
      "  rtranif1 r1(a, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "control input of pass-enable switch cannot be of "
                            "type 'event'",
                            4, "28.8"));
}

TEST(BidirectionalSwitchUdnt, TranRejectsBuiltinBeforeUdnt) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  wire a;\n"
      "  my_net b;\n"
      "  tran t1(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bidirectional pass switch cannot connect a "
                            "user-defined nettype to a built-in net",
                            5, "28.8"));
}

TEST(BidirectionalSwitchUdnt, Tranif0RejectsUdntWithBuiltin) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net a;\n"
      "  wire b, en;\n"
      "  tranif0 t1(a, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bidirectional pass switch cannot connect a "
                            "user-defined nettype to a built-in net",
                            5, "28.8"));
}

TEST(BidirectionalSwitchUdnt, EnabledSwitchesRejectDifferentUdnts) {
  for (const std::string& sw : {"tranif0", "tranif1"}) {
    std::string src =
        "module m;\n"
        "  nettype logic net_a;\n"
        "  nettype logic net_b;\n"
        "  net_a a;\n"
        "  net_b b;\n"
        "  wire en;\n  ";
    src += sw;
    src += " t1(a, b, en);\nendmodule\n";
    ElabFixture f;
    Elaborate(src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "bidirectional pass switch cannot connect "
                              "different user-defined nettypes ('net_a' and "
                              "'net_b')",
                              7, "28.8"))
        << sw;
  }
}

TEST(BidirectionalSwitchUdnt, Tranif0AcceptsSameUdntOnBothSides) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net a, b;\n"
      "  wire en;\n"
      "  tranif0 t1(a, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(BidirectionalSwitchControlType,
     DISABLED_ShortRealAndRealtimeControlsAreNamed) {
  const char* const kTypes[] = {"shortreal", "realtime"};
  for (const char* type : kTypes) {
    std::string src = "module m;\n  wire a, b;\n  ";
    src += type;
    src += " en;\n  rtranif1 t1(a, b, en);\nendmodule\n";
    ElabFixture f;
    Elaborate(src, f);
    std::string msg = "control input of pass-enable switch cannot be of type '";
    msg += type;
    msg += "'";
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), msg, 4, "28.8")) << type;
  }
}

TEST(BidirectionalSwitchControlType,
     DISABLED_Tranif1RejectsClassHandleControl) {
  ElabFixture f;
  Elaborate(
      "class c_t;\n"
      "endclass\n"
      "module m;\n"
      "  wire a, b;\n"
      "  c_t h;\n"
      "  tranif1 t1(a, b, h);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "control input of pass-enable switch cannot be of "
                            "type",
                            6, "28.8"));
}

TEST(BidirectionalSwitchControlType,
     DISABLED_ANettypeNetControlMustBeFourState) {
  const char* const kNettypes[] = {"bit", "real"};
  for (const char* type : kNettypes) {
    std::string src = "module m;\n  nettype ";
    src += type;
    src += " ctl_t;\n  wire a, b;\n  ctl_t en;\n  tranif1 t1(a, b, en);\n";
    src += "endmodule\n";
    ElabFixture f;
    Elaborate(src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "control input of pass-enable switch cannot be "
                              "of type",
                              5, "28.8"))
        << type;
  }
}

TEST(BidirectionalSwitchControlType, ALogicNettypeNetControlIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic ctl_t;\n"
      "  wire a, b;\n"
      "  ctl_t en;\n"
      "  tranif0 t1(a, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(BidirectionalSwitchTerminals, Rtranif1RejectsWholeVector) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [3:0] vec;\n"
      "  wire b, en;\n"
      "  rtranif1 r1(vec, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a resistive bidirectional pass switch terminal "
                            "connects to a single bit",
                            4, "28.8"));
}

TEST(BidirectionalSwitchTerminals, Rtranif0RejectsPartSelect) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [3:0] vec;\n"
      "  wire b, en;\n"
      "  rtranif0 r1(vec[2:1], b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a resistive bidirectional pass switch terminal "
                            "connects to a single bit",
                            4, "28.8"));
}

TEST(BidirectionalSwitchTerminals, RtranRejectsVariableTerminal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic a;\n"
      "  wire b;\n"
      "  rtran r1(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a resistive bidirectional pass switch terminal", 4,
                            "28.8"));
}

TEST(BidirectionalSwitchTerminals, Rtranif1RejectsConcatenationTerminal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire b, en;\n"
      "  rtranif1 r2({b, en}, b, en);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a resistive bidirectional pass switch terminal", 3,
                            "28.8"));
}

TEST(BidirectionalSwitchTerminals, ResistiveSwitchesAcceptBitSelects) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [3:0] vec;\n"
      "  wire b, en;\n"
      "  rtranif0 r1(vec[0], b, en);\n"
      "  rtranif1 r2(vec[1], vec[2], en);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
