
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

TEST(ClockingBlockParse, SingleSignalDecl) {
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

TEST(ClockingBlockParse, MultipleSignalDeclCommaSeparated) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a, b, c;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 3u);
  EXPECT_EQ(item->clocking_signals[0].name, "a");
  EXPECT_EQ(item->clocking_signals[1].name, "b");
  EXPECT_EQ(item->clocking_signals[2].name, "c");
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

TEST(ClockingBlockParse, InoutSignalParsed) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    inout data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInout);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
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

TEST(ClockingBlockParse, NegedgeEventExpr) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(negedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNegedge);
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

TEST(ClockingBlockParse, AllThreeDirections) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data_in;\n"
      "    output data_out;\n"
      "    inout bidir;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));

  VerifyClockingSignalDirections(item, {
                                           {Direction::kInput, "data_in"},
                                           {Direction::kOutput, "data_out"},
                                           {Direction::kInout, "bidir"},
                                       });
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

TEST(ClockingBlockParse, PlainNamedDecl) {
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
  EXPECT_EQ(item->kind, ModuleItemKind::kClockingBlock);
  EXPECT_EQ(item->name, "cb");
  EXPECT_FALSE(item->is_default_clocking);
  EXPECT_FALSE(item->is_global_clocking);
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

TEST(ClockingBlockParse, InputDirection) {
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
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
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

TEST(ClockingBlockParse, EndLabelAccepted) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cb @(posedge clk);\n"
              "    input a;\n"
              "  endclocking : cb\n"
              "endmodule\n"));
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

TEST(ClockingBlockParse, SignalDirectionsVerified) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data_in;\n"
      "    output data_out;\n"
      "    inout bidir;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));

  VerifyClockingSignalDirections(item, {
                                           {Direction::kInput, "data_in"},
                                           {Direction::kOutput, "data_out"},
                                           {Direction::kInout, "bidir"},
                                       });
}

TEST(ClockingBlockParse, MultipleInputsSameDirection) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data, ready, enable;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));

  const char* const kExpectedNames[] = {"data", "ready", "enable"};
  ASSERT_EQ(item->clocking_signals.size(), std::size(kExpectedNames));
  for (size_t i = 0; i < std::size(kExpectedNames); ++i) {
    EXPECT_EQ(item->clocking_signals[i].name, kExpectedNames[i])
        << "signal " << i;
    EXPECT_EQ(item->clocking_signals[i].direction, Direction::kInput)
        << "signal " << i;
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

TEST(ClockingBlockParse, MinimalSingleInput) {
  auto r = Parse(
      "module m;\n"
      "  clocking bus @(posedge clk);\n"
      "    input addr;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  EXPECT_EQ(item->kind, ModuleItemKind::kClockingBlock);
  EXPECT_EQ(item->name, "bus");
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kPosedge);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[0].name, "addr");
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

}  // namespace
TEST(ClockingBlockParse, NamedDeclNotDefaultNotGlobal) {
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
  EXPECT_EQ(item->kind, ModuleItemKind::kClockingBlock);
  EXPECT_EQ(item->name, "cb");
  EXPECT_FALSE(item->is_default_clocking);
  EXPECT_FALSE(item->is_global_clocking);
}

TEST(ClockingBlockParse, InputOutputCombinedDirection) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #2 output #4 data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInout);
}

TEST(ClockingBlockParse, EndLabelSimple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking : cb\n"
              "endmodule\n"));
}
