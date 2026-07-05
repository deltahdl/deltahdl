
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ClockingBlockParse, OutputDirection) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kOutput);
  EXPECT_EQ(item->clocking_signals[0].name, "ack");
}

TEST(ClockingBlockParse, MixedDirectionSignals) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data_in;\n"
      "    output data_out;\n"
      "    inout ctrl;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 3u);

  struct Expected {
    Direction dir;
    const char* name;
  };
  const Expected kExpected[] = {
      {Direction::kInput, "data_in"},
      {Direction::kOutput, "data_out"},
      {Direction::kInout, "ctrl"},
  };
  for (size_t i = 0; i < std::size(kExpected); ++i) {
    EXPECT_EQ(item->clocking_signals[i].direction, kExpected[i].dir)
        << "signal " << i;
    EXPECT_EQ(item->clocking_signals[i].name, kExpected[i].name)
        << "signal " << i;
  }
}

TEST(ClockingBlockParse, InoutDirection) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    inout bidir;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInout);
  EXPECT_EQ(item->clocking_signals[0].name, "bidir");
}

TEST(ClockingBlockParse, NegedgeClockEvent) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(negedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNegedge);
}

TEST(ClockingBlockParse, BusExampleFullDecl) {
  auto r = Parse(
      "module t;\n"
      "  clocking bus @(posedge clock1);\n"
      "    default input #10ns output #2ns;\n"
      "    input data, ready, enable = top.mem1.enable;\n"
      "    output negedge ack;\n"
      "    input #1step addr;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_EQ(item->name, "bus");

  ASSERT_EQ(item->clocking_signals.size(), 5u);

  EXPECT_EQ(item->clocking_signals[0].name, "data");
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[1].name, "ready");
  EXPECT_EQ(item->clocking_signals[1].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[2].name, "enable");
  EXPECT_EQ(item->clocking_signals[2].direction, Direction::kInput);
  ASSERT_NE(item->clocking_signals[2].hier_expr, nullptr);
  EXPECT_EQ(item->clocking_signals[3].name, "ack");
  EXPECT_EQ(item->clocking_signals[3].direction, Direction::kOutput);
  EXPECT_EQ(item->clocking_signals[3].skew_edge, Edge::kNegedge);
  EXPECT_EQ(item->clocking_signals[4].name, "addr");
  EXPECT_EQ(item->clocking_signals[4].direction, Direction::kInput);
}

TEST(ClockingBlockParse, BareSignalNoHierExpr) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
  EXPECT_EQ(item->clocking_signals[0].hier_expr, nullptr);
}

TEST(ClockingBlockParse, BasicDeclWithInputOutput) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a;\n"
      "    output b;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_EQ(item->name, "cb");
  EXPECT_FALSE(item->is_default_clocking);
  EXPECT_FALSE(item->is_global_clocking);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kPosedge);
  ASSERT_EQ(item->clocking_signals.size(), 2u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[0].name, "a");
  EXPECT_EQ(item->clocking_signals[1].direction, Direction::kOutput);
  EXPECT_EQ(item->clocking_signals[1].name, "b");
}

TEST(ClockingBlockParse, MultipleDirectionGroups) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a;\n"
      "    output b;\n"
      "    inout c;\n"
      "    input #2 output #4 d;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 4u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[1].direction, Direction::kOutput);
  EXPECT_EQ(item->clocking_signals[2].direction, Direction::kInout);
  EXPECT_EQ(item->clocking_signals[3].direction, Direction::kInout);
}

TEST(ClockingBlockParse, BareIdentifierEvent) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNone);
}

TEST(ClockingBlockParse, MultipleSignalsSameDirectionList) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data, ready, enable;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));

  const char* const kNames[] = {"data", "ready", "enable"};
  ASSERT_EQ(item->clocking_signals.size(), std::size(kNames));
  for (size_t i = 0; i < std::size(kNames); ++i) {
    EXPECT_EQ(item->clocking_signals[i].name, kNames[i]) << "signal " << i;
    EXPECT_EQ(item->clocking_signals[i].direction, Direction::kInput)
        << "signal " << i;
  }
}

TEST(ClockingBlockParse, PropertyDeclInsideBlock) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "    property p;\n"
      "      data;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
}

TEST(ClockingBlockParse, EndLabelMatches) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking : cb\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "cb");
}

TEST(ClockingBlockParse, EventBareIdentifierNoEdge) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @clk;\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNone);
}

TEST(ClockingBlockParse, EventParenthesizedPosedge) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kPosedge);
}

TEST(ClockingBlockParse, MultipleBlocksInModule) {
  auto r = Parse(
      "module t;\n"
      "  clocking cd1 @(posedge phi1);\n"
      "    input data;\n"
      "    output write;\n"
      "  endclocking\n"
      "  clocking cd2 @(posedge phi2);\n"
      "    input #2 output #4 cmd;\n"
      "    input enable;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* cb1 = FindClockingBlockByIndex(r, 0);
  auto* cb2 = FindClockingBlockByIndex(r, 1);
  ASSERT_NE(cb1, nullptr);
  ASSERT_NE(cb2, nullptr);
  EXPECT_EQ(cb1->name, "cd1");
  EXPECT_EQ(cb2->name, "cd2");
}

TEST(ClockingBlockParse, BasicNamedBlockAllFields) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_EQ(r.cu->modules.size(), 1u);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  ASSERT_EQ(item->clocking_signals.size(), 1u);

  struct {
    bool ok;
    const char* label;
  } const kChecks[] = {
      {item->kind == ModuleItemKind::kClockingBlock, "kind"},
      {item->name == "cb", "name"},
      {!item->is_default_clocking, "not_default"},
      {!item->is_global_clocking, "not_global"},
      {item->clocking_event[0].edge == Edge::kPosedge, "event_edge"},
      {item->clocking_signals[0].direction == Direction::kInput, "sig_dir"},
      {item->clocking_signals[0].name == "data", "sig_name"},
  };
  for (const auto& c : kChecks) {
    EXPECT_TRUE(c.ok) << c.label;
  }
}

TEST(ClockingBlockParse, BlockAmongOtherModuleItems) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  logic [7:0] data;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "cb");

  ASSERT_GE(r.cu->modules[0]->items.size(), 4u);
}

TEST(ClockingBlockParse, EdgeKeywordAsSkewEdge) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input edge data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[0].skew_edge, Edge::kEdge);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
}

TEST(ClockingBlockParse, DefaultSkewParsed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    default input #10 output #2;\n"
              "    input data;\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingBlockParse, EmptyBodyAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingSkewParse, CombinedInputOutputSkewDelays) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #2 output #4 cmd;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kInout);
  EXPECT_EQ(sig.name, "cmd");
  EXPECT_NE(sig.skew_delay, nullptr);
  EXPECT_NE(sig.out_skew_delay, nullptr);
}

TEST(ClockingSkewParse, InputAndOutputNumericSkews) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #1 data_in;\n"
      "    output #2 data_out;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 2u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  ASSERT_NE(item->clocking_signals[0].skew_delay, nullptr);
  EXPECT_EQ(item->clocking_signals[1].direction, Direction::kOutput);
  ASSERT_NE(item->clocking_signals[1].skew_delay, nullptr);
}

TEST(ClockingSkewParse, OutputNegedgeWithDelay) {
  auto r = Parse(
      "module foo(input phi1, input [7:0] data);\n"
      "  clocking dram @(posedge phi1);\n"
      "    input data;\n"
      "    output negedge #1 address;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 2u);
  auto& out_sig = item->clocking_signals[1];
  EXPECT_EQ(out_sig.direction, Direction::kOutput);
  EXPECT_EQ(out_sig.name, "address");
  EXPECT_EQ(out_sig.skew_edge, Edge::kNegedge);
  ASSERT_NE(out_sig.skew_delay, nullptr);
}

TEST(ClockingSkewParse, EdgeOnlyNoDelay) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output posedge ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.skew_edge, Edge::kPosedge);
  EXPECT_EQ(sig.skew_delay, nullptr);
}

TEST(ClockingSkewParse, DelayOnlyNoEdge) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #3 data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.skew_edge, Edge::kNone);
  ASSERT_NE(sig.skew_delay, nullptr);
  EXPECT_EQ(sig.skew_delay->kind, ExprKind::kIntegerLiteral);
}

TEST(ClockingSkewParse, OneStepDelayText) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #1step data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  ASSERT_NE(sig.skew_delay, nullptr);
  EXPECT_EQ(sig.skew_delay->text, "1step");
}

TEST(ClockingSkewParse, InputEdgeAndDelayNoOutput) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input posedge #2 data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kInput);
  EXPECT_EQ(sig.skew_edge, Edge::kPosedge);
  ASSERT_NE(sig.skew_delay, nullptr);
}

TEST(ClockingSkewParse, InputNumericSkewOnly) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #2 data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kInput);
  EXPECT_EQ(sig.name, "data");
  ASSERT_NE(sig.skew_delay, nullptr);
  EXPECT_EQ(sig.skew_delay->kind, ExprKind::kIntegerLiteral);
}

TEST(ClockingSkewParse, OutputNegedgeEdgeOnly) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(posedge clk);\n"
      "    output negedge ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kOutput);
  EXPECT_EQ(sig.name, "ack");
  EXPECT_EQ(sig.skew_edge, Edge::kNegedge);
}

TEST(ClockingSkewParse, OneStepWithHierExpr) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cd1 @(posedge phi1);\n"
              "    input #1step state = top.cpu1.state;\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingSkewParse, ExplicitZeroSkew) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cb @(posedge clk);\n"
              "    input #0 data;\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingSkewParse, MixedTimeUnitSuffix) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cd2 @(posedge phi2);\n"
              "    input #2 output #4ps cmd;\n"
              "    input enable;\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingSkewParse, ExplicitZeroOutputSkew) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output #0 data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kOutput);
  ASSERT_NE(item->clocking_signals[0].skew_delay, nullptr);
}

TEST(ClockingSkewParse, DramExampleFromSpec) {
  auto r = Parse(
      "module m;\n"
      "  clocking dram @(clk);\n"
      "    input #1ps address;\n"
      "    input #5 output #6 data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 2u);
  EXPECT_EQ(item->clocking_signals[0].name, "address");
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[1].name, "data");
  EXPECT_EQ(item->clocking_signals[1].direction, Direction::kInout);
}

TEST(ClockingSkewParse, InputSkewMultipleSignals) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(negedge clk);\n"
      "    input #1 a, b, c;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(item->clocking_signals[i].direction, Direction::kInput)
        << "signal " << i;
    ASSERT_NE(item->clocking_signals[i].skew_delay, nullptr) << "signal " << i;
  }
}

TEST(ClockingSkewParse, DefaultInputSkew) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    default input #1;\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
}

TEST(ClockingSkewParse, DefaultOutputSkew) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    default output #2;\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "ack");
}

// clocking_declaration second alternative: `global clocking [id] event ;
// endclocking`. The global form carries no clocking_item body, so no signals
// are recorded and the global flag is set.
TEST(ClockingBlockParse, GlobalClockingDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  global clocking gclk @(posedge clk);\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_FALSE(item->is_default_clocking);
  EXPECT_EQ(item->name, "gclk");
  EXPECT_EQ(item->clocking_signals.size(), 0u);
}

// clocking_declaration first alternative with the optional `default` prefix and
// a clocking_event: `default clocking [id] event ; { clocking_item }
// endclocking`. Distinct from the bodyless `default clocking id ;` form.
TEST(ClockingBlockParse, DefaultClockingWithEvent) {
  auto r = Parse(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_FALSE(item->is_global_clocking);
  EXPECT_EQ(item->name, "cb");
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
}

// Negative: clocking_declaration requires a clocking_event after the (optional)
// identifier for a non-default block. A bare `clocking id ;` has no event and
// must be rejected.
TEST(ClockingBlockParse, MissingClockingEventRejected) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb;\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// clocking_drive ::= clockvar_expression <= [ cycle_delay ] expression.
// Without a cycle_delay the drive is a nonblocking assignment whose lvalue is a
// clockvar_expression (`cb.data`, a member access), with no cycle delay set.
TEST(ClockingDriveParse, DriveWithoutCycleDelay) {
  auto r = Parse(
      "module m;\n"
      "  initial cb.data <= 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s = FirstInitialStmt(r);
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(s->lhs, nullptr);
  EXPECT_EQ(s->lhs->kind, ExprKind::kMemberAccess);
  EXPECT_EQ(s->cycle_delay, nullptr);
}

// cycle_delay ::= ## integral_number. The `##2` before the expression records
// an integer-literal cycle delay on the drive.
TEST(ClockingDriveParse, DriveWithCycleDelayInteger) {
  auto r = Parse(
      "module m;\n"
      "  initial cb.data <= ##2 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s = FirstInitialStmt(r);
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(s->cycle_delay, nullptr);
  EXPECT_EQ(s->cycle_delay->kind, ExprKind::kIntegerLiteral);
}

// cycle_delay ::= ## identifier. The delay may name a constant instead of a
// literal, e.g. `##n`.
TEST(ClockingDriveParse, DriveWithCycleDelayIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial cb.data <= ##n 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s = FirstInitialStmt(r);
  ASSERT_NE(s, nullptr);
  ASSERT_NE(s->cycle_delay, nullptr);
  EXPECT_EQ(s->cycle_delay->kind, ExprKind::kIdentifier);
}

// cycle_delay ::= ## ( expression ). A parenthesized expression delay, e.g.
// `##(a + 1)`, parses to the enclosed expression tree.
TEST(ClockingDriveParse, DriveWithCycleDelayParenExpr) {
  auto r = Parse(
      "module m;\n"
      "  initial cb.data <= ##(a + 1) 8'hFF;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s = FirstInitialStmt(r);
  ASSERT_NE(s, nullptr);
  ASSERT_NE(s->cycle_delay, nullptr);
  EXPECT_EQ(s->cycle_delay->kind, ExprKind::kBinary);
}

// clockvar_expression ::= clockvar select. A bit-select applied to the clockvar
// (`cb.data[3]`) makes the drive lvalue a select over the member access.
TEST(ClockingDriveParse, ClockvarExpressionWithSelect) {
  auto r = Parse(
      "module m;\n"
      "  initial cb.data[3] <= 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* s = FirstInitialStmt(r);
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->kind, StmtKind::kNonblockingAssign);
  ASSERT_NE(s->lhs, nullptr);
  EXPECT_EQ(s->lhs->kind, ExprKind::kSelect);
}

// clocking_declaration: the clocking_identifier is optional. An anonymous
// clocking block (no name before the event) is accepted and records an empty
// name.
TEST(ClockingBlockParse, AnonymousClockingBlock) {
  auto r = Parse(
      "module m;\n"
      "  clocking @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->name.empty());
  EXPECT_FALSE(item->is_global_clocking);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
}

// clocking_declaration second alternative: the clocking_identifier is likewise
// optional for `global clocking`.
TEST(ClockingBlockParse, AnonymousGlobalClocking) {
  auto r = Parse(
      "module m;\n"
      "  global clocking @(posedge clk);\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_TRUE(item->name.empty());
}

// clocking_item third alternative admits an assertion_item_declaration; a
// sequence declaration is one such input form.
TEST(ClockingBlockParse, SequenceDeclInsideBlock) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a, b;\n"
      "    sequence s;\n"
      "      a ##1 b;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 2u);
}

// clocking_item third alternative: a let declaration is also a valid
// assertion_item_declaration inside a clocking block.
TEST(ClockingBlockParse, LetDeclInsideBlock) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "    let val = 42;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
}

// clocking_item third alternative: the assertion_item_declaration may be
// preceded by attribute_instance(s).
TEST(ClockingBlockParse, AttributedAssertionItemInBlock) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "    (* foo *) property p;\n"
      "      data;\n"
      "    endproperty\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
}

// Negative: {attribute_instance} is grammatical only before the
// assertion_item_declaration alternative of clocking_item, not before a
// clocking_direction, so an attributed signal direction is rejected.
TEST(ClockingBlockParse, AttributeBeforeDirectionRejected) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    (* foo *) input data;\n"
      "  endclocking\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// Negative: the inout alternative of clocking_direction admits no
// clocking_skew, so a skew before an inout signal is rejected.
TEST(ClockingBlockParse, InoutWithSkewRejected) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    inout #1 data;\n"
      "  endclocking\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
