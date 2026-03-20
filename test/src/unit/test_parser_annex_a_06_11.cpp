
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- ClockingBlockParse: clocking_declaration, clocking_direction,
//     clocking_decl_assign ---

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

// --- ClockingSkewParse: clocking_skew, default_skew ---

TEST(ClockingSkewParse, OneStepDelay) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    input #1step data;\n"
              "  endclocking\n"
              "endmodule"));
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

TEST(ClockingSkewParse, OneStepInClockingBlock) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #1step a;\n"
      "  endclocking\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];

  ModuleItem* clk_item = nullptr;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kClockingBlock) {
      clk_item = item;
      break;
    }
  }
  ASSERT_NE(clk_item, nullptr);
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

TEST(ClockingSkewParse, EdgeAndDelayTogether) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output negedge #1 ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlockByIndex(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.skew_edge, Edge::kNegedge);
  ASSERT_NE(sig.skew_delay, nullptr);
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

TEST(ClockingSkewParse, NonzeroInputSkew) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #3 addr;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kInput);
  EXPECT_EQ(sig.name, "addr");
  ASSERT_NE(sig.skew_delay, nullptr);
  EXPECT_EQ(sig.skew_delay->kind, ExprKind::kIntegerLiteral);
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

TEST(ClockingSkewParse, CombinedInputOutputVerified) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #2 output #4 cmd;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kInout);
  EXPECT_EQ(sig.name, "cmd");
  EXPECT_NE(sig.skew_delay, nullptr);
  EXPECT_NE(sig.out_skew_delay, nullptr);
}

TEST(ClockingSkewParse, TimeUnitSuffix) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking dram @(clk);\n"
              "    input #1ps address;\n"
              "    input #5 output #6 data;\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingSkewParse, OneStepWithHierExpr) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cd1 @(posedge phi1);\n"
              "    input #1step state = top.cpu1.state;\n"
              "  endclocking\n"
              "endmodule\n"));
}

TEST(ClockingSkewParse, OutputNegedgeDelayAccepted) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cb @(posedge clk);\n"
              "    output negedge #1 address;\n"
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

TEST(ClockingSkewParse, InputSkewDelayFields) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #2 data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  ASSERT_NE(sig.skew_delay, nullptr);

  struct {
    bool ok;
    const char* label;
  } const kChecks[] = {
      {sig.direction == Direction::kInput, "direction"},
      {sig.name == "data", "name"},
      {sig.skew_delay->kind == ExprKind::kIntegerLiteral, "skew_delay_kind"},
  };
  for (const auto& c : kChecks) {
    EXPECT_TRUE(c.ok) << c.label;
  }
}

TEST(ClockingSkewParse, CombinedSkewBothPresent) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #2 output #4 cmd;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlockChecked(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kInout);
  EXPECT_EQ(sig.name, "cmd");

  const void* const kSkewPtrs[] = {sig.skew_delay, sig.out_skew_delay};
  for (const auto* p : kSkewPtrs) {
    EXPECT_NE(p, nullptr);
  }
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

TEST(ClockingSkewParse, OneStepDelayStructure) {
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
  EXPECT_NE(item->clocking_signals[0].skew_delay, nullptr);
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

TEST(ClockingSkewParse, OutputNegedgeSkewEdgeVerified) {
  auto r = Parse(
      "module m;\n"
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

// --- CycleDelayParse: cycle_delay ---

TEST(CycleDelayParse, IntegralNumber) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
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

// --- DefaultClockingParse: default clocking declaration ---

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

TEST(DefaultClockingParse, SeparateReferenceStatement) {
  auto r = Parse(
      "module t;\n"
      "  clocking busA @(posedge clk1);\n"
      "    input data;\n"
      "  endclocking\n"
      "  default clocking busA;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  bool found_ref = false;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kClockingBlock &&
        item->is_default_clocking && item->clocking_event.empty()) {
      EXPECT_EQ(item->name, "busA");
      found_ref = true;
    }
  }
  EXPECT_TRUE(found_ref);
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

// --- GlobalClockingParse: global clocking declaration ---

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

// --- SyncDriveParse: clocking_drive, clockvar, clockvar_expression ---

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

TEST(SyncDriveParse, CycleDelayNumber) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    output data;\n"
              "  endclocking\n"
              "  initial cb.data <= ##3 8'h42;\n"
              "endmodule\n"));
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

// --- Additional coverage ---

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
  EXPECT_TRUE(
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

}  // namespace
