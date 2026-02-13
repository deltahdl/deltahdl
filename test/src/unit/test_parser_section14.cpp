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
    if (item->kind != ModuleItemKind::kClockingBlock)
      continue;
    if (count == idx)
      return item;
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
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
  auto r = Parse("module m;\n"
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
