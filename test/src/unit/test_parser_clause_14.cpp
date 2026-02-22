#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

struct ParseResult14 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult14 Parse(const std::string &src) {
  ParseResult14 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem *FindClockingBlock(ParseResult14 &r, size_t idx = 0) {
  size_t count = 0;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kClockingBlock) continue;
    if (count == idx) return item;
    ++count;
  }
  return nullptr;
}

// Validates parse result and retrieves a clocking block via output param.
// Must be called through ASSERT_NO_FATAL_FAILURE.
static void GetClockingBlock(ParseResult14 &r, ModuleItem *&out,
                             size_t idx = 0) {
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  out = FindClockingBlock(r, idx);
  ASSERT_NE(out, nullptr);
}

// =============================================================================
// §14.3 — Basic clocking block declaration
// =============================================================================

TEST(ParserSection14, BasicClockingBlock) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_EQ(r.cu->modules.size(), 1u);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  ASSERT_EQ(item->clocking_signals.size(), 1u);

  // Validate properties, event, and signal via loop.
  struct {
    bool ok;
    const char *label;
  } const kChecks[] = {
      {item->kind == ModuleItemKind::kClockingBlock, "kind"},
      {item->name == "cb", "name"},
      {!item->is_default_clocking, "not_default"},
      {!item->is_global_clocking, "not_global"},
      {item->clocking_event[0].edge == Edge::kPosedge, "event_edge"},
      {item->clocking_signals[0].direction == Direction::kInput, "sig_dir"},
      {item->clocking_signals[0].name == "data", "sig_name"},
  };
  for (const auto &c : kChecks) {
    EXPECT_TRUE(c.ok) << c.label;
  }
}

// =============================================================================
// §14.3 — Default clocking
// =============================================================================

TEST(ParserSection14, DefaultClocking) {
  auto r = Parse(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_FALSE(item->is_global_clocking);
  EXPECT_EQ(item->name, "cb");

  struct Expected {
    Direction dir;
    std::string name;
  };
  Expected expected[] = {
      {Direction::kInput, "data"},
      {Direction::kOutput, "ack"},
  };
  ASSERT_EQ(item->clocking_signals.size(), std::size(expected));
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(item->clocking_signals[i].direction, expected[i].dir)
        << "signal " << i;
    EXPECT_EQ(item->clocking_signals[i].name, expected[i].name)
        << "signal " << i;
  }
}

// =============================================================================
// §14.14 — Global clocking
// =============================================================================

TEST(ParserSection14, GlobalClocking) {
  auto r = Parse(
      "module m;\n"
      "  global clocking gclk @(posedge sys_clk);\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_EQ(item->name, "gclk");
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_FALSE(item->is_default_clocking);
  EXPECT_TRUE(item->clocking_signals.empty());
}

// =============================================================================
// §14.3 — Signal directions: input, output, inout
// =============================================================================

TEST(ParserSection14, SignalDirections) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data_in;\n"
      "    output data_out;\n"
      "    inout bidir;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));

  struct Expected {
    Direction dir;
    std::string name;
  };
  Expected expected[] = {
      {Direction::kInput, "data_in"},
      {Direction::kOutput, "data_out"},
      {Direction::kInout, "bidir"},
  };
  ASSERT_EQ(item->clocking_signals.size(), std::size(expected));
  for (size_t i = 0; i < std::size(expected); ++i) {
    EXPECT_EQ(item->clocking_signals[i].direction, expected[i].dir)
        << "signal " << i;
    EXPECT_EQ(item->clocking_signals[i].name, expected[i].name)
        << "signal " << i;
  }
}

// =============================================================================
// §14.3 — Input skew with delay
// =============================================================================

TEST(ParserSection14, InputSkewDelay) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #2 data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto &sig = item->clocking_signals[0];
  ASSERT_NE(sig.skew_delay, nullptr);

  struct {
    bool ok;
    const char *label;
  } const kChecks[] = {
      {sig.direction == Direction::kInput, "direction"},
      {sig.name == "data", "name"},
      {sig.skew_delay->kind == ExprKind::kIntegerLiteral, "skew_delay_kind"},
  };
  for (const auto &c : kChecks) {
    EXPECT_TRUE(c.ok) << c.label;
  }
}

// =============================================================================
// §14.3 — Output skew with edge
// =============================================================================

TEST(ParserSection14, OutputSkewEdge) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    output negedge ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto &sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kOutput);
  EXPECT_EQ(sig.name, "ack");
  EXPECT_EQ(sig.skew_edge, Edge::kNegedge);
}

// =============================================================================
// §14.3 — Multiple signals in one direction group
// =============================================================================

TEST(ParserSection14, MultipleSignalsSameDirection) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data, ready, enable;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));

  const char *const kExpectedNames[] = {"data", "ready", "enable"};
  ASSERT_EQ(item->clocking_signals.size(), std::size(kExpectedNames));
  for (size_t i = 0; i < std::size(kExpectedNames); ++i) {
    EXPECT_EQ(item->clocking_signals[i].name, kExpectedNames[i])
        << "signal " << i;
    EXPECT_EQ(item->clocking_signals[i].direction, Direction::kInput)
        << "signal " << i;
  }
}

// =============================================================================
// §14.5 — Hierarchical expression assignment
// =============================================================================

TEST(ParserSection14, HierarchicalExpression) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input enable = top.mem1.enable;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "enable");
  ASSERT_NE(item->clocking_signals[0].hier_expr, nullptr);
}

// =============================================================================
// §14.3 — Combined input/output skews
// =============================================================================

TEST(ParserSection14, CombinedInputOutputSkew) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #2 output #4 cmd;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto &sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kInout);
  EXPECT_EQ(sig.name, "cmd");

  const void *const kSkewPtrs[] = {sig.skew_delay, sig.out_skew_delay};
  for (const auto *p : kSkewPtrs) {
    EXPECT_NE(p, nullptr);
  }
}

// =============================================================================
// §14.3 — Clocking block with end label
// =============================================================================

TEST(ParserSection14, EndLabel) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking : cb\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "cb");
}

// =============================================================================
// §14.3 — Clocking block in module context alongside other items
// =============================================================================

TEST(ParserSection14, ClockingBlockAmongOtherItems) {
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
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "cb");
  // Also check the other items parsed.
  ASSERT_GE(r.cu->modules[0]->items.size(), 4u);
}

// =============================================================================
// §14.3 — Unnamed default clocking block
// =============================================================================

TEST(ParserSection14, UnnamedDefaultClocking) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_TRUE(item->name.empty());
}

// =============================================================================
// §14.8 — Multiple clocking blocks
// =============================================================================

TEST(ParserSection14, MultipleClockingBlocks) {
  auto r = Parse(
      "module m;\n"
      "  clocking cd1 @(posedge phi1);\n"
      "    input data;\n"
      "  endclocking\n"
      "  clocking cd2 @(posedge phi2);\n"
      "    output cmd;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *cb1 = FindClockingBlock(r, 0);
  auto *cb2 = FindClockingBlock(r, 1);
  ASSERT_NE(cb1, nullptr);
  ASSERT_NE(cb2, nullptr);
  EXPECT_EQ(cb1->name, "cd1");
  EXPECT_EQ(cb2->name, "cd2");
}

// =============================================================================
// §14.3 — Clocking event with bare identifier (no edge)
// =============================================================================

TEST(ParserSection14, ClockingEventBareIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNone);
}

// =============================================================================
// LRM section 14.1 -- Clocking block overview
// =============================================================================

// §14.1 introduces clocking blocks as grouping clock-synchronous signals.
// A minimal clocking block with a single input validates the core construct.
TEST(ParserSection14, OverviewMinimalClockingBlock) {
  auto r = Parse(
      "module m;\n"
      "  clocking bus @(posedge clk);\n"
      "    input addr;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_EQ(item->kind, ModuleItemKind::kClockingBlock);
  EXPECT_EQ(item->name, "bus");
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kPosedge);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[0].name, "addr");
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
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 3u);

  struct Expected {
    Direction dir;
    const char *name;
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

// §14.1 overview: clocking block with negedge event.
TEST(ParserSection14, OverviewNegedgeClockEvent) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(negedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNegedge);
}

// §14.1 overview: clocking block with input skew and output skew together.
TEST(ParserSection14, OverviewInputOutputSkews) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #1 data_in;\n"
      "    output #2 data_out;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 2u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  ASSERT_NE(item->clocking_signals[0].skew_delay, nullptr);
  EXPECT_EQ(item->clocking_signals[1].direction, Direction::kOutput);
  ASSERT_NE(item->clocking_signals[1].skew_delay, nullptr);
}

// =============================================================================
// LRM section 14.10 -- Clocking block events
// =============================================================================

// §14.10: clocking block event used in always block (from LRM example).
// The clocking block name itself acts as an event trigger in the Observed
// region. This tests the LRM example: always @(dram) $display(...);
TEST(ParserSection14, ClockingBlockEventAlwaysAt) {
  auto r = Parse(
      "module foo(input phi1, input [7:0] data);\n"
      "  clocking dram @(posedge phi1);\n"
      "    input data;\n"
      "  endclocking\n"
      "  always @(dram)\n"
      "    $display(\"clocking block event\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "dram");
  // The always block should also have been parsed (at least 2 items).
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

// §14.10: clocking block with output negedge skew (from LRM example).
TEST(ParserSection14, ClockingBlockEventOutputNegedgeSkew) {
  auto r = Parse(
      "module foo(input phi1, input [7:0] data);\n"
      "  clocking dram @(posedge phi1);\n"
      "    input data;\n"
      "    output negedge #1 address;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 2u);
  auto &out_sig = item->clocking_signals[1];
  EXPECT_EQ(out_sig.direction, Direction::kOutput);
  EXPECT_EQ(out_sig.name, "address");
  EXPECT_EQ(out_sig.skew_edge, Edge::kNegedge);
  ASSERT_NE(out_sig.skew_delay, nullptr);
}

// §14.10: clocking event alongside a posedge always block.
TEST(ParserSection14, ClockingBlockEventWithPosedgeAlways) {
  auto r = Parse(
      "module m;\n"
      "  clocking dram @(posedge phi1);\n"
      "    input data;\n"
      "  endclocking\n"
      "  always @(posedge phi1) $display(\"clocking event\");\n"
      "  always @(dram) $display(\"clocking block event\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  // Three items: clocking block + two always blocks.
  EXPECT_GE(r.cu->modules[0]->items.size(), 3u);
}

// §14.10: clocking block with multiple input signals triggers one event.
TEST(ParserSection14, ClockingBlockEventMultipleInputs) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input a, b, c;\n"
      "  endclocking\n"
      "  always @(cb) $display(\"triggered\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 3u);
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

// =============================================================================
// LRM section 14.12 -- Default clocking
// =============================================================================

// §14.12: default clocking with negedge (variation of the LRM examples).
TEST(ParserSection14, DefaultClockingNegedge) {
  auto r = Parse(
      "module m;\n"
      "  default clocking cb @(negedge clk);\n"
      "    input data;\n"
      "    output ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNegedge);
  ASSERT_EQ(item->clocking_signals.size(), 2u);
}

// §14.12: default clocking block with end label.
TEST(ParserSection14, DefaultClockingEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  default clocking bus @(posedge clk);\n"
      "    input data;\n"
      "  endclocking : bus\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_EQ(item->name, "bus");
}

// §14.12: unnamed default clocking block with multiple signals.
TEST(ParserSection14, DefaultClockingUnnamedMultipleSignals) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk);\n"
      "    input a, b;\n"
      "    output c;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_TRUE(item->name.empty());
  ASSERT_EQ(item->clocking_signals.size(), 3u);
}

// =============================================================================
// LRM section 14.13 -- Input sampling
// =============================================================================

// §14.13: input sampled at clocking event (basic pattern from LRM).
// Validates: clocking cb @(negedge clk); input v; endclocking
TEST(ParserSection14, InputSamplingBasic) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(negedge clk);\n"
      "    input v;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[0].name, "v");
  EXPECT_EQ(item->clocking_signals[0].skew_delay, nullptr);
}

// §14.13: input with explicit #0 skew (samples in the Observed region).
TEST(ParserSection14, InputSamplingExplicitZeroSkew) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #0 data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto &sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kInput);
  ASSERT_NE(sig.skew_delay, nullptr);
  EXPECT_EQ(sig.skew_delay->kind, ExprKind::kIntegerLiteral);
}

// §14.13: inout signals are also sampled as inputs at the clocking event.
TEST(ParserSection14, InputSamplingInoutSignal) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    inout data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInout);
  EXPECT_EQ(item->clocking_signals[0].name, "data");
}

// §14.13: input with nonzero skew samples from a prior time step.
TEST(ParserSection14, InputSamplingNonzeroSkew) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #3 addr;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto &sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kInput);
  EXPECT_EQ(sig.name, "addr");
  ASSERT_NE(sig.skew_delay, nullptr);
  EXPECT_EQ(sig.skew_delay->kind, ExprKind::kIntegerLiteral);
}

// §14.13: multiple inputs with same skew declaration.
TEST(ParserSection14, InputSamplingMultipleSignals) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(negedge clk);\n"
      "    input #1 a, b, c;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(item->clocking_signals[i].direction, Direction::kInput)
        << "signal " << i;
    ASSERT_NE(item->clocking_signals[i].skew_delay, nullptr) << "signal " << i;
  }
}

// =============================================================================
// LRM section 14.14 -- Global clocking
// =============================================================================

// §14.14: global clocking with compound event expression (from LRM example).
TEST(ParserSection14, GlobalClockingCompoundEvent) {
  auto r = Parse(
      "module top;\n"
      "  logic clk1, clk2;\n"
      "  global clocking sys @(clk1 or clk2); endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_EQ(item->name, "sys");
  EXPECT_TRUE(item->clocking_signals.empty());
  EXPECT_GE(item->clocking_event.size(), 2u);
}

// §14.14: global clocking with unnamed identifier (name is optional).
TEST(ParserSection14, GlobalClockingUnnamed) {
  auto r = Parse(
      "module m;\n"
      "  global clocking @(posedge sys_clk); endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_TRUE(item->name.empty());
  EXPECT_TRUE(item->clocking_signals.empty());
}

// §14.14: global clocking with end label.
TEST(ParserSection14, GlobalClockingEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  global clocking gclk @(posedge sys_clk);\n"
      "  endclocking : gclk\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_EQ(item->name, "gclk");
}

// §14.14: global clocking has no signal declarations (shall be empty body).
TEST(ParserSection14, GlobalClockingNoSignals) {
  auto r = Parse(
      "module m;\n"
      "  global clocking gc @(negedge clk); endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_TRUE(item->clocking_signals.empty());
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNegedge);
}

// §14.14: global clocking in subsystem pattern (from LRM hierarchical example).
TEST(ParserSection14, GlobalClockingSubsystemPattern) {
  auto r = Parse(
      "module subsystem1;\n"
      "  logic subclk1;\n"
      "  global clocking sub_sys1 @(subclk1); endclocking\n"
      "endmodule\n");
  ModuleItem *item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_global_clocking);
  EXPECT_EQ(item->name, "sub_sys1");
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kNone);
}
