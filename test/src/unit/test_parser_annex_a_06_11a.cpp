
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ClockingSkewParse, DefaultInputOutputSkew) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    default input #1 output #2;\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->clocking_signals.size(), 1u);
}

TEST(ClockingSkewParse, DefaultSkewWithTimeUnits) {
  auto r = Parse(
      "module t;\n"
      "  clocking bus @(posedge clock1);\n"
      "    default input #10ns output #2ns;\n"
      "    input data, ready;\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));

  ASSERT_GE(item->clocking_signals.size(), 3u);
}

TEST(ClockingSkewParse, DefaultInputOnlyAccepted) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cb @(posedge clk);\n"
              "    default input #5;\n"
              "    input a;\n"
              "    output b;\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingSkewParse, DefaultOutputOnlyAccepted) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cb @(posedge clk);\n"
              "    default output #3;\n"
              "    input a;\n"
              "    output b;\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingSkewParse, DefaultOneStepInputNegedgeOutput) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking ck1 @(posedge clk);\n"
              "    default input #1step output negedge;\n"
              "    input a;\n"
              "    output b;\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingSkewParse, DefaultSkewWithPerSignalOverride) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking bus @(posedge clock1);\n"
              "    default input #10ns output #2ns;\n"
              "    input data, ready, enable = top.mem1.enable;\n"
              "    output negedge ack;\n"
              "    input #1step addr;\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingSkewParse, DefaultSkewNoEdgeEvent) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking ck2 @(clk);\n"
              "    default input #1step output negedge;\n"
              "    input a;\n"
              "    output b;\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingSkewParse, DefaultSkewNumericLiterals) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cb @(posedge clk);\n"
              "    default input #3 output #7;\n"
              "    input x;\n"
              "    output y;\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingSkewParse, DefaultInputOutputBothAccepted) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    default input #1 output #2;\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CycleDelayParse, Identifier) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##n;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CycleDelayParse, ParenthesizedExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##(j + 1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CycleDelayParse, ZeroCycleDelay) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CycleDelayParse, CycleDelayInClockingDrive) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    cb.data <= ##n 8'h42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CycleDelayParse, CycleDelayStmtKind) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  auto& items = r.cu->modules[0]->items;
  ASSERT_FALSE(items.empty());
  auto* body = items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_FALSE(body->stmts.empty());
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kCycleDelay);
  EXPECT_NE(body->stmts[0]->cycle_delay, nullptr);
}

TEST(CycleDelayParse, WithDefaultClocking) {
  EXPECT_TRUE(
      ParseOk("program test(input logic clk, input logic [15:0] data);\n"
              "  default clocking bus @(posedge clk);\n"
              "    inout data;\n"
              "  endclocking\n"
              "  initial begin\n"
              "    ##5;\n"
              "    if (bus.data == 10)\n"
              "      ##1;\n"
              "  end\n"
              "endprogram\n"));
}

TEST(DefaultClockingParse, InlineWithNegedge) {
  auto r = Parse(
      "module m;\n"
      "  default clocking cb @(negedge clk);\n"
      "    input data;\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNegedge);
  ASSERT_EQ(item->clocking_signals.size(), 2u);
}

TEST(DefaultClockingParse, EndLabel) {
  auto r = Parse(
      "module m;\n"
      "  default clocking bus @(posedge clk);\n"
      "    input data;\n"
      "  endclocking : bus\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_EQ(item->name, "bus");
}

TEST(DefaultClockingParse, UnnamedWithMultipleSignals) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk);\n"
      "    input a, b;\n"
      "    output c;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_TRUE(item->name.empty());
  ASSERT_EQ(item->clocking_signals.size(), 3u);
}

TEST(DefaultClockingParse, ReferenceForm) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  bool found_ref = false;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_default_clocking && item->clocking_event.empty()) {
      EXPECT_EQ(item->name, "cb");
      found_ref = true;
    }
  }
  EXPECT_TRUE(found_ref);
}

TEST(DefaultClockingParse, AsModuleItem) {
  auto r = Parse(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kClockingBlock);
  EXPECT_TRUE(r.cu->modules[0]->items[0]->is_default_clocking);
}

TEST(DefaultClockingParse, InlineInoutDirection) {
  auto r = Parse(
      "module t;\n"
      "  default clocking bus @(posedge clk);\n"
      "    inout data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_EQ(item->name, "bus");
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInout);
}

TEST(DefaultClockingParse, UnnamedInline) {
  auto r = Parse(
      "module t;\n"
      "  default clocking @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_TRUE(item->name.empty());
}

TEST(DefaultClockingParse, NamedWithIsDefaultAndNotGlobal) {
  auto r = Parse(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_FALSE(item->is_global_clocking);
  EXPECT_EQ(item->name, "cb");
}

TEST(DefaultClockingParse, InInterface) {
  EXPECT_TRUE(
      ParseOk("interface my_if (input clk);\n"
              "  logic [7:0] data;\n"
              "  default clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endinterface\n"));
}

TEST(DefaultClockingParse, InProgram) {
  EXPECT_TRUE(
      ParseOk("program test(input logic clk);\n"
              "  default clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endprogram\n"));
}

TEST(DefaultClockingParse, DuplicateDefaultClockingParses) {
  auto r = Parse(
      "module m;\n"
      "  default clocking cb1 @(posedge clk1);\n"
      "    input a;\n"
      "  endclocking\n"
      "  default clocking cb2 @(posedge clk2);\n"
      "    input b;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  size_t default_count = 0;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_default_clocking)
      ++default_count;
  }
  EXPECT_EQ(default_count, 2u);
}

TEST(GlobalClockingParse, BasicNamedPosedge) {
  auto r = Parse(
      "module t;\n"
      "  global clocking gclk @(posedge sys_clk);\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_EQ(item->name, "gclk");
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_FALSE(item->is_default_clocking);
  EXPECT_TRUE(item->clocking_signals.empty());
}

TEST(GlobalClockingParse, CompoundOrEvent) {
  auto r = Parse(
      "module t;\n"
      "  global clocking sys @(clk1 or clk2);\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_GE(item->clocking_event.size(), 2u);
}

TEST(GlobalClockingParse, EndLabel) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  global clocking gclk @(posedge clk);\n"
              "  endclocking : gclk\n"
              "endmodule\n"));
}

TEST(GlobalClockingParse, NoSignalsAllowed) {
  auto r = Parse(
      "module m;\n"
      "  global clocking gc @(negedge clk); endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_TRUE(item->clocking_signals.empty());
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNegedge);
}

TEST(GlobalClockingParse, SubsystemPattern) {
  auto r = Parse(
      "module subsystem1;\n"
      "  logic subclk1;\n"
      "  global clocking sub_sys1 @(subclk1); endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_EQ(item->name, "sub_sys1");
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNone);
}

TEST(GlobalClockingParse, UnnamedGlobalClocking) {
  auto r = Parse(
      "module m;\n"
      "  global clocking @(negedge clk); endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_TRUE(item->name.empty());
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNegedge);
}

TEST(GlobalClockingParse, InInterface) {
  EXPECT_TRUE(
      ParseOk("interface my_if (input clk);\n"
              "  global clocking gc @(posedge clk); endclocking\n"
              "endinterface\n"));
}

TEST(GlobalClockingParse, InProgram) {
  EXPECT_TRUE(
      ParseOk("program test(input logic clk);\n"
              "  global clocking gc @(posedge clk); endclocking\n"
              "endprogram\n"));
}

TEST(GlobalClockingParse, DuplicateGlobalClockingParses) {
  auto r = Parse(
      "module m;\n"
      "  global clocking gc1 @(posedge clk1); endclocking\n"
      "  global clocking gc2 @(posedge clk2); endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  size_t global_count = 0;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_global_clocking)
      ++global_count;
  }
  EXPECT_EQ(global_count, 2u);
}

TEST(GlobalClockingParse, GlobalClockSystemFunctionCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  global clocking gc @(posedge clk); endclocking\n"
              "  always @($global_clock) begin\n"
              "  end\n"
              "endmodule\n"));
}

TEST(GlobalClockingParse, NotDefaultNotGlobal) {
  auto r = Parse(
      "module m;\n"
      "  global clocking gclk @(posedge sys_clk);\n"
      "  endclocking\n"
      "endmodule\n");
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_FALSE(item->is_default_clocking);
}

TEST(SyncDriveParse, SimpleClockingDrive) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    cb.data <= 8'hFF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(SyncDriveParse, WithCycleDelay) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    cb.data <= ##2 8'hFF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(stmt->cycle_delay, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

TEST(SyncDriveParse, CycleDelayParenExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    output data;\n"
              "  endclocking\n"
              "  initial cb.data <= ##(n+1) 8'h42;\n"
              "endmodule\n"));
}

TEST(SyncDriveParse, ClockvarBitSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking dom @(posedge clk);\n"
              "    output sig;\n"
              "  endclocking\n"
              "  initial dom.sig[2] <= 1'b1;\n"
              "endmodule\n"));
}

TEST(SyncDriveParse, ClockvarPartSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking bus @(posedge clk);\n"
              "    output data;\n"
              "  endclocking\n"
              "  initial bus.data[3:0] <= 4'h5;\n"
              "endmodule\n"));
}

TEST(SyncDriveParse, InoutClockvarDrive) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    inout data;\n"
              "  endclocking\n"
              "  initial cb.data <= 8'hAB;\n"
              "endmodule\n"));
}

TEST(SyncDriveParse, MultipleDrivesInBlock) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output a, b;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    cb.a <= 1;\n"
      "    cb.b <= 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SyncDriveParse, CycleDelayIdentifier) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    output data;\n"
              "  endclocking\n"
              "  initial cb.data <= ##n 8'h42;\n"
              "endmodule\n"));
}

TEST(ClockingBlockParse, SequenceDeclInsideBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "    sequence s;\n"
              "      data;\n"
              "    endsequence\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingBlockParse, LetDeclInsideBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "    let my_let = data;\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingBlockParse, InInterface) {
  EXPECT_TRUE(
      ParseOk("interface my_if (input clk);\n"
              "  logic [7:0] data;\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endinterface\n"));
}

TEST(ClockingBlockParse, InProgram) {
  EXPECT_TRUE(
      ParseOk("program test(input logic clk);\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endprogram\n"));
}

TEST(ClockingBlockParse, ErrorMissingClockingEvent) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  clocking cb;\n"
              "    input data;\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingBlockParse, ErrorMissingEndclocking) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "endmodule\n"));
}

TEST(ClockingBlockParse, EndLabelMismatchAccepted) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking : wrong_name\n"
              "endmodule\n"));
}

TEST(ClockingSkewParse, OutputEdgeKeyword) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output edge ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kOutput);
  EXPECT_EQ(item->clocking_signals[0].skew_edge, Edge::kEdge);
}

TEST(ClockingSkewParse, OutputPosedgeWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output posedge #3 ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kOutput);
  EXPECT_EQ(sig.skew_edge, Edge::kPosedge);
  ASSERT_NE(sig.skew_delay, nullptr);
}

TEST(ClockingSkewParse, DefaultInputEdgeAndDelay) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    default input posedge #5;\n"
              "    input data;\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingSkewParse, DefaultSkewFieldsStored) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    default input #10 output #2;\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  ASSERT_NE(item->default_input_skew_delay, nullptr);
  EXPECT_EQ(item->default_input_skew_delay->kind, ExprKind::kIntegerLiteral);
  ASSERT_NE(item->default_output_skew_delay, nullptr);
  EXPECT_EQ(item->default_output_skew_delay->kind, ExprKind::kIntegerLiteral);
}

TEST(ClockingSkewParse, DefaultInputOnlyFieldStored) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    default input #5;\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  ASSERT_NE(item->default_input_skew_delay, nullptr);
  EXPECT_EQ(item->default_output_skew_delay, nullptr);
}

TEST(ClockingSkewParse, DefaultOutputOnlyFieldStored) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    default output #3;\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_EQ(item->default_input_skew_delay, nullptr);
  ASSERT_NE(item->default_output_skew_delay, nullptr);
}

TEST(ClockingBlockParse, AttributedPropertyDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "    (* annotated *) property p;\n"
              "      data;\n"
              "    endproperty\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingBlockParse, AttributedSequenceDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "    (* tag = 1 *) sequence s;\n"
              "      data;\n"
              "    endsequence\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingBlockParse, AttributedLetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "    (* foo *) let my_let = data;\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(GlobalClockingParse, RejectsClockingItems) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  global clocking gc @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endmodule\n"));
}

}  // namespace
