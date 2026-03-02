// §14.3: Clocking block declaration

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.6.11 clocking_direction — output
// =============================================================================
TEST(ParserA611, ClockingDirectionOutput) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kOutput);
  EXPECT_EQ(item->clocking_signals[0].name, "ack");
}

// --- Test helpers ---
struct ParseResult15 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult15 Parse(const std::string& src) {
  ParseResult15 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// §14.1 overview: clocking block with multiple direction groups.
TEST(ParserSection14, OverviewMixedDirectionSignals) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data_in;\n"
      "    output data_out;\n"
      "    inout ctrl;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
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

// =============================================================================
// A.6.11 clocking_direction — inout
// =============================================================================
TEST(ParserA611, ClockingDirectionInout) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    inout bidir;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInout);
  EXPECT_EQ(item->clocking_signals[0].name, "bidir");
}

// §14.1 overview: clocking block with negedge event.
TEST(ParserSection14, OverviewNegedgeClockEvent) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(negedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNegedge);
}

// =============================================================================
// A.6.11 list_of_clocking_decl_assign — single signal
// =============================================================================
TEST(ParserA611, ListOfClockingDeclAssignSingle) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
}

struct ParseResult21 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult21 Parse(const std::string& src) {
  ParseResult21 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// Full LRM example: bus clocking block with default skew,
// hierarchical expression, per-signal overrides, and 1step.
TEST(ParserSection19, FullExample_BusClockingBlock) {
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
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_EQ(item->name, "bus");
  // Note: default skew is parsed but not stored in the AST.
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

// =============================================================================
// A.6.11 list_of_clocking_decl_assign — multiple comma-separated signals
// =============================================================================
TEST(ParserA611, ListOfClockingDeclAssignMultiple) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a, b, c;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 3u);
  EXPECT_EQ(item->clocking_signals[0].name, "a");
  EXPECT_EQ(item->clocking_signals[1].name, "b");
  EXPECT_EQ(item->clocking_signals[2].name, "c");
}

// =============================================================================
// A.6.11 clocking_decl_assign — signal_identifier only
// =============================================================================
TEST(ParserA611, ClockingDeclAssignBare) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
  EXPECT_EQ(item->clocking_signals[0].hier_expr, nullptr);
}

// §14.13: inout signals are also sampled as inputs at the clocking event.
TEST(ParserSection14, InputSamplingInoutSignal) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    inout data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInout);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
}

// §14.13: multiple inputs with same skew declaration.
TEST(ParserSection14, InputSamplingMultipleSignals) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(negedge clk);\n"
      "    input #1 a, b, c;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(item->clocking_signals[i].direction, Direction::kInput)
        << "signal " << i;
    ASSERT_NE(item->clocking_signals[i].skew_delay, nullptr) << "signal " << i;
  }
}

struct ParseResult19 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult19 Parse(const std::string& src) {
  ParseResult19 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem* FindClockingBlock(ParseResult19& r, size_t idx = 0) {
  size_t count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kClockingBlock) continue;
    if (count == idx) return item;
    ++count;
  }
  return nullptr;
}

// Validates parse result and retrieves a clocking block via output param.
// Must be called through ASSERT_NO_FATAL_FAILURE.
static void GetClockingBlock(ParseResult19& r, ModuleItem*& out,
                             size_t idx = 0) {
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  out = FindClockingBlock(r, idx);
  ASSERT_NE(out, nullptr);
}

// =============================================================================
// LRM section 19.4 -- Clocking blocks
// =============================================================================
// Basic clocking block with posedge event, input and output signals.
TEST(ParserSection19, ClockingBlock_BasicDecl) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a;\n"
      "    output b;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
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

// =============================================================================
// A.6.11 clocking_declaration — multiple direction groups
// =============================================================================
TEST(ParserA611, MultipleDirectionGroups) {
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
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 4u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[1].direction, Direction::kOutput);
  EXPECT_EQ(item->clocking_signals[2].direction, Direction::kInout);
  EXPECT_EQ(item->clocking_signals[3].direction, Direction::kInout);
}

// Clocking block with negedge event.
TEST(ParserSection19, ClockingBlock_NegedgeEvent) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(negedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNegedge);
}

// Clocking block with bare identifier event (no edge).
TEST(ParserSection19, ClockingBlock_BareIdentifierEvent) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNone);
}

// Clocking block with all three signal directions: input, output, inout.
TEST(ParserSection19, ClockingBlock_AllDirections) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data_in;\n"
      "    output data_out;\n"
      "    inout bidir;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));

  VerifyClockingSignalDirections(item, {
                                           {Direction::kInput, "data_in"},
                                           {Direction::kOutput, "data_out"},
                                           {Direction::kInout, "bidir"},
                                       });
}

// Multiple signals in a single direction group, comma-separated.
TEST(ParserSection19, ClockingBlock_MultipleSignalsSameDirection) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data, ready, enable;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));

  const char* const kNames[] = {"data", "ready", "enable"};
  ASSERT_EQ(item->clocking_signals.size(), std::size(kNames));
  for (size_t i = 0; i < std::size(kNames); ++i) {
    EXPECT_EQ(item->clocking_signals[i].name, kNames[i]) << "signal " << i;
    EXPECT_EQ(item->clocking_signals[i].direction, Direction::kInput)
        << "signal " << i;
  }
}

// =============================================================================
// A.6.11 clocking_item — assertion_item_declaration (property_declaration)
// =============================================================================
TEST(ParserA611, ClockingItemPropertyDecl) {
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
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
}

// =============================================================================
// A.6.11 clocking_item — assertion_item_declaration (let_declaration)
// =============================================================================
TEST(ParserA611, ClockingItemLetDecl) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "    let valid = data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
}

static ModuleItem* FindClockingBlock(ParseResult& r, size_t idx = 0) {
  size_t count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kClockingBlock) continue;
    if (count == idx) return item;
    ++count;
  }
  return nullptr;
}

// =============================================================================
// A.6.11 clocking_declaration — plain clocking block
// =============================================================================
TEST(ParserA611, ClockingDeclPlain) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kClockingBlock);
  EXPECT_EQ(item->name, "cb");
  EXPECT_FALSE(item->is_default_clocking);
  EXPECT_FALSE(item->is_global_clocking);
}

// =============================================================================
// A.6.11 clocking_declaration — end label
// =============================================================================
TEST(ParserA611, ClockingDeclEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking : cb\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "cb");
}

// =============================================================================
// A.6.11 clocking_declaration — clocking_event as @identifier
// =============================================================================
TEST(ParserA611, ClockingEventBareIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @clk;\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNone);
}

// =============================================================================
// A.6.11 clocking_declaration — clocking_event as @(event_expression)
// =============================================================================
TEST(ParserA611, ClockingEventParenExpr) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kPosedge);
}

// =============================================================================
// A.6.11 clocking_item — default default_skew (input)
// =============================================================================
TEST(ParserA611, ClockingItemDefaultSkewInput) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    default input #1;\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
}

// =============================================================================
// A.6.11 clocking_item — default default_skew (output)
// =============================================================================
TEST(ParserA611, ClockingItemDefaultSkewOutput) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    default output #2;\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "ack");
}

// =============================================================================
// A.6.11 clocking_item — default default_skew (input + output)
// =============================================================================
TEST(ParserA611, ClockingItemDefaultSkewInputOutput) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    default input #1 output #2;\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->clocking_signals.size(), 1u);
}

// =============================================================================
// A.6.11 clocking_direction — input
// =============================================================================
TEST(ParserA611, ClockingDirectionInput) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
}

// Multiple clocking blocks in the same module (different clocks).
TEST(ParserSection19, ClockingBlockScope_MultipleBlocks) {
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
  auto* cb1 = FindClockingBlock(r, 0);
  auto* cb2 = FindClockingBlock(r, 1);
  ASSERT_NE(cb1, nullptr);
  ASSERT_NE(cb2, nullptr);
  EXPECT_EQ(cb1->name, "cd1");
  EXPECT_EQ(cb2->name, "cd2");
}

// =============================================================================
// LRM section 19.6.1.2 -- Default skew
// =============================================================================
// Default input and output skews with time-unit literals.
TEST(ParserSection19, DefaultSkew_InputOutputTimeUnits) {
  auto r = Parse(
      "module t;\n"
      "  clocking bus @(posedge clock1);\n"
      "    default input #10ns output #2ns;\n"
      "    input data, ready;\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  // Note: default skew is parsed but not stored in the AST.
  ASSERT_GE(item->clocking_signals.size(), 3u);
}

// Default input skew only (no output skew specified).
TEST(ParserSection19, DefaultSkew_InputOnly) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cb @(posedge clk);\n"
              "    default input #5;\n"
              "    input a;\n"
              "    output b;\n"
              "  endclocking\n"
              "endmodule\n"));
}

// Default output skew only (no input skew specified).
TEST(ParserSection19, DefaultSkew_OutputOnly) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cb @(posedge clk);\n"
              "    default output #3;\n"
              "    input a;\n"
              "    output b;\n"
              "  endclocking\n"
              "endmodule\n"));
}

// Default input #1step with output negedge.
TEST(ParserSection19, DefaultSkew_1StepInputNegedgeOutput) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking ck1 @(posedge clk);\n"
              "    default input #1step output negedge;\n"
              "    input a;\n"
              "    output b;\n"
              "  endclocking\n"
              "endmodule\n"));
}

}  // namespace
