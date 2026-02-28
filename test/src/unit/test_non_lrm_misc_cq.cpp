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

TEST(ParserSection18, RandomizeWithRestrictedIdList) {
  auto r = Parse(
      "class C;\n"
      "  rand integer x;\n"
      "endclass\n"
      "function int F(int y);\n"
      "  C obj;\n"
      "  F = obj.randomize() with (x) { x < y; };\n"
      "endfunction\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, StdRandomizeWithMultipleVars) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    int x, y;\n"
      "    std::randomize(x, y) with { x + y < 100; x > 0; y > 0; };\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// =============================================================================
// §18.13.3 srandom() -- random stability and process
// =============================================================================
TEST(ParserSection18, SrandomMethodCall) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void seed_it();\n"
      "    this.srandom(42);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, SrandomInInitialBlock) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    process p;\n"
      "    p = process::self();\n"
      "    p.srandom(123);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection18, SrandomWithExpression) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void seed_it(int seed_val);\n"
      "    this.srandom(seed_val + 1);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// =============================================================================
// §18.13.4 get_randstate()
// =============================================================================
TEST(ParserSection18, GetRandstateCall) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function string save_state();\n"
      "    return this.get_randstate();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, GetRandstateAssignToVar) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    process p;\n"
      "    string state;\n"
      "    p = process::self();\n"
      "    state = p.get_randstate();\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection18, GetRandstateInFunction) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void checkpoint(output string s);\n"
      "    s = this.get_randstate();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// =============================================================================
// §18.13.5 set_randstate()
// =============================================================================
TEST(ParserSection18, SetRandstateCall) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void restore_state(string state);\n"
      "    this.set_randstate(state);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18, SetRandstateInInitialBlock) {
  auto r = Parse(
      "module top;\n"
      "  initial begin\n"
      "    process p;\n"
      "    string saved;\n"
      "    p = process::self();\n"
      "    saved = p.get_randstate();\n"
      "    p.set_randstate(saved);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection18, GetSetRandstateRoundtrip) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  function void save_and_restore();\n"
      "    string s;\n"
      "    s = this.get_randstate();\n"
      "    this.randomize();\n"
      "    this.set_randstate(s);\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// =============================================================================
// LRM section 18.5.3 -- Distribution constraints (additional tests)
// =============================================================================
TEST(ParserSection18b, DistEqualWeightSingleValue) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {42 := 1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18b, DistDivideWeightMultipleValues) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {1 :/ 1, 2 :/ 1, 3 :/ 1, 4 :/ 1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18b, DistWithRangeAndEqualWeight) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[0:3] := 1, [4:7] := 2}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18b, DistWithMixedWeightTypes) {
  // Mix of := and :/ in the same distribution
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {0 := 1, [1:10] :/ 5, 11 := 3}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18b, DistWithDefaultWeight) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {[0:255] :/ 1, default :/ 1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18b, DistInsideIfConstraint) {
  // Distribution inside a conditional constraint block
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  rand bit mode;\n"
      "  constraint c {\n"
      "    if (mode == 0) {\n"
      "      x dist {[0:10] := 1};\n"
      "    } else {\n"
      "      x dist {[100:200] := 1};\n"
      "    }\n"
      "  }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18b, DistWithExpressionWeights) {
  // Weights can be arbitrary constant expressions
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {1 := 2 * 3, 2 := 4 + 1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18b, DistWithNegativeValues) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x dist {-10 := 1, 0 := 2, 10 := 1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ParserSection18b, DistMultipleConstraints) {
  // Multiple dist constraints in one class
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  constraint cx { x dist {[0:100] := 1}; }\n"
      "  constraint cy { y dist {[0:50] :/ 2, [51:100] :/ 1}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
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
// LRM section 19.5 -- Clocking block events
// =============================================================================
// Use a clocking block name as an event in an always block.
TEST(ParserSection19, ClockingBlockEvent_AlwaysAt) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking dram @(posedge phi1);\n"
              "    input data;\n"
              "  endclocking\n"
              "  always @(dram)\n"
              "    $display(\"clocking block event\");\n"
              "endmodule\n"));
}

// Clocking event used alongside a posedge always for comparison.
TEST(ParserSection19, ClockingBlockEvent_BothTriggers) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking dram @(posedge phi1);\n"
              "    input data;\n"
              "    output negedge #1 address;\n"
              "  endclocking\n"
              "  always @(posedge phi1) $display(\"clocking event\");\n"
              "  always @(dram) $display(\"clocking block event\");\n"
              "endmodule\n"));
}

// Clocking block event used in an initial block with @(cb).
TEST(ParserSection19, ClockingBlockEvent_InitialBlock) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cb @(posedge clk);\n"
              "    input v;\n"
              "  endclocking\n"
              "  initial begin\n"
              "    @(cb);\n"
              "    $display(cb.v);\n"
              "  end\n"
              "endmodule\n"));
}

// Access clocking block signal via dot notation (cb.v) in always block.
TEST(ParserSection19, ClockingBlockEvent_DotAccess) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  clocking cb @(negedge clk);\n"
              "    input v;\n"
              "  endclocking\n"
              "  always @(cb) $display(cb.v);\n"
              "endmodule\n"));
}

// =============================================================================
// LRM section 19.5.1 -- Default clocking
// =============================================================================
// Declaring a clocking block inline as default.
TEST(ParserSection19, DefaultClocking_InlineDecl) {
  auto r = Parse(
      "module t;\n"
      "  default clocking bus @(posedge clk);\n"
      "    inout data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_EQ(item->name, "bus");
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInout);
}

// Unnamed default clocking block.
TEST(ParserSection19, DefaultClocking_Unnamed) {
  auto r = Parse(
      "module t;\n"
      "  default clocking @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "endmodule\n");
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_TRUE(item->is_default_clocking);
  EXPECT_TRUE(item->name.empty());
}

// Assigning an existing clocking block as default via a separate statement.
TEST(ParserSection19, DefaultClocking_SeparateStatement) {
  auto r = Parse(
      "module t;\n"
      "  clocking busA @(posedge clk1);\n"
      "    input data;\n"
      "  endclocking\n"
      "  default clocking busA;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  // The reference form creates a second clocking block item.
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

// Default clocking in an interface.
TEST(ParserSection19, DefaultClocking_InInterface) {
  EXPECT_TRUE(
      ParseOk("interface my_if (input clk);\n"
              "  logic [7:0] data;\n"
              "  default clocking cb @(posedge clk);\n"
              "    input data;\n"
              "  endclocking\n"
              "endinterface\n"));
}

// =============================================================================
// LRM section 19.5.2 -- Clocking block scope
// =============================================================================
// Clocking block coexists with other module items (variables, always blocks).
TEST(ParserSection19, ClockingBlockScope_AmongOtherItems) {
  auto r = Parse(
      "module t;\n"
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
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "cb");
  ASSERT_GE(r.cu->modules[0]->items.size(), 4u);
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
