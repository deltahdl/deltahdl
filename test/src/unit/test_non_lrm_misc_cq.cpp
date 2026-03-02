// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

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

namespace {

// Clocking block in a program with initial block accessing signals.
TEST(ParserSection19, ClockingBlockScope_ProgramAccess) {
  EXPECT_TRUE(
      ParseOk("program test_prog(\n"
              "  input phi1, input [15:0] data, output logic write,\n"
              "  input phi2, inout [8:1] cmd, input enable\n"
              ");\n"
              "  clocking cd1 @(posedge phi1);\n"
              "    input data;\n"
              "    output write;\n"
              "    input state = top.cpu1.state;\n"
              "  endclocking\n"
              "  clocking cd2 @(posedge phi2);\n"
              "    input #2 output #4ps cmd;\n"
              "    input enable;\n"
              "  endclocking\n"
              "  initial begin\n"
              "    @(cd1);\n"
              "  end\n"
              "endprogram\n"));
}

// Clocking block in an interface (valid scope per LRM).
TEST(ParserSection19, ClockingBlockScope_InInterface) {
  EXPECT_TRUE(
      ParseOk("interface bus_if (input clk);\n"
              "  logic [7:0] data;\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endinterface\n"));
}

// Clocking block in a checker (valid scope per LRM).
TEST(ParserSection19, ClockingBlockScope_InChecker) {
  EXPECT_TRUE(
      ParseOk("checker my_check(input clk, input data);\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endchecker\n"));
}

// =============================================================================
// LRM section 19.6.1 -- Input and output skews
// =============================================================================
// Input skew with numeric delay.
TEST(ParserSection19, InputOutputSkew_InputNumeric) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #2 data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kInput);
  EXPECT_EQ(sig.name, "data");
  ASSERT_NE(sig.skew_delay, nullptr);
  EXPECT_EQ(sig.skew_delay->kind, ExprKind::kIntegerLiteral);
}

// Output skew with edge qualifier.
TEST(ParserSection19, InputOutputSkew_OutputEdge) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(posedge clk);\n"
      "    output negedge ack;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kOutput);
  EXPECT_EQ(sig.name, "ack");
  EXPECT_EQ(sig.skew_edge, Edge::kNegedge);
}

// Combined input and output skews on a single signal.
TEST(ParserSection19, InputOutputSkew_CombinedInputOutput) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(posedge clk);\n"
      "    input #2 output #4 cmd;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kInout);
  EXPECT_EQ(sig.name, "cmd");
  EXPECT_NE(sig.skew_delay, nullptr);
  EXPECT_NE(sig.out_skew_delay, nullptr);
}

// Input skew with time-unit suffix (e.g., #1ps).
TEST(ParserSection19, InputOutputSkew_TimeUnitSuffix) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking dram @(clk);\n"
              "    input #1ps address;\n"
              "    input #5 output #6 data;\n"
              "  endclocking\n"
              "endmodule\n"));
}

// Input skew of #1step (special 1step literal).
TEST(ParserSection19, InputOutputSkew_OneStep) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cd1 @(posedge phi1);\n"
              "    input #1step state = top.cpu1.state;\n"
              "  endclocking\n"
              "endmodule\n"));
}

// Output skew with negedge and numeric delay combined.
TEST(ParserSection19, InputOutputSkew_OutputNegedgeWithDelay) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cb @(posedge clk);\n"
              "    output negedge #1 address;\n"
              "  endclocking\n"
              "endmodule\n"));
}

// Input skew with explicit #0 (Observed region sampling).
TEST(ParserSection19, InputOutputSkew_ExplicitZero) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cb @(posedge clk);\n"
              "    input #0 data;\n"
              "  endclocking\n"
              "endmodule\n"));
}

// Combined input/output with time-unit suffix on output (#4ps).
TEST(ParserSection19, InputOutputSkew_MixedUnitSuffix) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cd2 @(posedge phi2);\n"
              "    input #2 output #4ps cmd;\n"
              "    input enable;\n"
              "  endclocking\n"
              "endmodule\n"));
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

// Default skew with per-signal override: addr overrides input to #1step.
TEST(ParserSection19, DefaultSkew_PerSignalOverride) {
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

// Default skew on a clocking block with no edge in the event.
TEST(ParserSection19, DefaultSkew_NoEdgeEvent) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking ck2 @(clk);\n"
              "    default input #1step output negedge;\n"
              "    input a;\n"
              "    output b;\n"
              "  endclocking\n"
              "endmodule\n"));
}

// Default skew with numeric literals (no time-unit suffix).
TEST(ParserSection19, DefaultSkew_NumericLiterals) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cb @(posedge clk);\n"
              "    default input #3 output #7;\n"
              "    input x;\n"
              "    output y;\n"
              "  endclocking\n"
              "endmodule\n"));
}

// =============================================================================
// Additional cross-cutting tests
// =============================================================================
// End label on clocking block.
TEST(ParserSection19, ClockingBlock_EndLabel) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cb @(posedge clk);\n"
              "    input a;\n"
              "  endclocking : cb\n"
              "endmodule\n"));
}

// Hierarchical expression assignment to a clocking signal.
TEST(ParserSection19, ClockingBlock_HierarchicalExpr) {
  auto r = Parse(
      "module t;\n"
      "  clocking cb @(posedge clk);\n"
      "    input enable = top.mem1.enable;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].name, "enable");
  ASSERT_NE(item->clocking_signals[0].hier_expr, nullptr);
}

}  // namespace
