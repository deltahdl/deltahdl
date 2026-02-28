// §14.10: Clocking block events

#include "fixture_parser.h"

using namespace delta;

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

namespace {

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
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "dram");
  // The always block should also have been parsed (at least 2 items).
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
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
  auto* item = FindClockingBlock(r);
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
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 3u);
  EXPECT_GE(r.cu->modules[0]->items.size(), 2u);
}

}  // namespace
