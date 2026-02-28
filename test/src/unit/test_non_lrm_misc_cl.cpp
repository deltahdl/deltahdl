// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult14 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult14 Parse(const std::string& src) {
  ParseResult14 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static ModuleItem* FindClockingBlock(ParseResult14& r, size_t idx = 0) {
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
static void GetClockingBlock(ParseResult14& r, ModuleItem*& out,
                             size_t idx = 0) {
  ASSERT_NE(r.cu, nullptr);
  ASSERT_FALSE(r.cu->modules.empty());
  out = FindClockingBlock(r, idx);
  ASSERT_NE(out, nullptr);
}

namespace {

// Named and positional arguments cannot be mixed in the same call.
// This test verifies that a purely named call parses with correct count.
TEST(ParserSection13, NamedArgBindingAllNamed) {
  auto r = Parse(
      "module m;\n"
      "  function int add(int a, int b, int c);\n"
      "    return a + b + c;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = add(.c(3), .a(1), .b(2));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
  ASSERT_EQ(stmt->rhs->arg_names.size(), 3u);
  EXPECT_EQ(stmt->rhs->arg_names[0], "c");
  EXPECT_EQ(stmt->rhs->arg_names[1], "a");
  EXPECT_EQ(stmt->rhs->arg_names[2], "b");
}

// =============================================================================
// LRM §13.8 -- Parameterized tasks and functions
// =============================================================================
// §13.8: A virtual class with type parameters and a static method serves as
// a parameterized subroutine.
TEST(ParserSection13, Sec13_8_VirtualClassStaticTask) {
  auto r = Parse(
      "virtual class C#(parameter W = 8);\n"
      "  static task drive(input logic [W-1:0] data);\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_virtual);
  EXPECT_EQ(r.cu->classes[0]->name, "C");
  ASSERT_EQ(r.cu->classes[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->params[0].first, "W");
}

// §13.8: Multiple parameters with defaults.
TEST(ParserSection13, Sec13_8_MultipleParamsWithDefaults) {
  auto r = Parse(
      "virtual class Codec#(parameter IN_W = 8,\n"
      "                     parameter OUT_W = $clog2(IN_W));\n"
      "  static function logic [OUT_W-1:0] encode(\n"
      "      input logic [IN_W-1:0] data);\n"
      "    encode = '0;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_EQ(r.cu->classes[0]->params.size(), 2u);
  EXPECT_EQ(r.cu->classes[0]->params[0].first, "IN_W");
  EXPECT_EQ(r.cu->classes[0]->params[1].first, "OUT_W");
}

// §13.8: Class scope resolution call with parameterization.
TEST(ParserSection13, Sec13_8_ScopeCallParsesAsExpr) {
  auto r = Parse(
      "module top;\n"
      "  logic [7:0] d;\n"
      "  logic [2:0] e;\n"
      "  assign e = Codec#(8)::encode(d);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §13.8: Two different specializations in the same module.
TEST(ParserSection13, Sec13_8_TwoSpecializations) {
  auto r = Parse(
      "module m;\n"
      "  logic [3:0] a4;\n"
      "  logic [15:0] a16;\n"
      "  logic [1:0] r4;\n"
      "  logic [3:0] r16;\n"
      "  assign r4  = C#(4)::ENCODER_f(a4);\n"
      "  assign r16 = C#(16)::ENCODER_f(a16);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §13.8: Three parameters with complex expressions.
TEST(ParserSection13, Sec13_8_ThreeParams) {
  auto r = Parse(
      "virtual class Xform#(parameter IN_W = 8,\n"
      "                     parameter OUT_W = IN_W * 2,\n"
      "                     parameter DEPTH = 4);\n"
      "  static function logic [OUT_W-1:0] widen(\n"
      "      input logic [IN_W-1:0] data);\n"
      "    return {DEPTH{data}};\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes[0]->params.size(), 3u);
}

// §13.8: Specialization with multiple parameter overrides.
TEST(ParserSection13, Sec13_8_MultiParamSpecialization) {
  auto r = Parse(
      "module m;\n"
      "  logic [15:0] data;\n"
      "  logic [31:0] result;\n"
      "  assign result = Xform#(16, 32, 2)::widen(data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §13.8: Virtual class with both static function and static task.
TEST(ParserSection13, Sec13_8_MixedStaticFuncAndTask) {
  auto r = Parse(
      "virtual class Utils#(parameter N = 4);\n"
      "  static function int max_val();\n"
      "    return (1 << N) - 1;\n"
      "  endfunction\n"
      "  static task report();\n"
      "    $display(\"N=%0d\", N);\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes[0]->members.size(), 2u);
}

// §13.8: Parameterized class with type parameter.
TEST(ParserSection13, Sec13_8_TypeParameter) {
  EXPECT_TRUE(
      ParseOk("virtual class Converter#(parameter type T = int);\n"
              "  static function T identity(input T val);\n"
              "    return val;\n"
              "  endfunction\n"
              "endclass\n"));
}

// §13.8: Call to parameterized class with type parameter override.
TEST(ParserSection13, Sec13_8_TypeParamOverrideCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] x, y;\n"
              "  assign y = Converter#(logic [7:0])::identity(x);\n"
              "endmodule\n"));
}

// §13.8: Static method with return value used in expression.
TEST(ParserSection13, Sec13_8_StaticMethodInExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int val;\n"
              "  assign val = Utils#(8)::max_val() + 1;\n"
              "endmodule\n"));
}

// §13.8: Static method with no arguments.
TEST(ParserSection13, Sec13_8_StaticMethodNoArgs) {
  auto r = Parse(
      "virtual class Constants#(parameter N = 32);\n"
      "  static function int zero();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// §13.8: Static method with multiple arguments of parameterized width.
TEST(ParserSection13, Sec13_8_MultiArgParameterizedWidth) {
  EXPECT_TRUE(
      ParseOk("virtual class Arith#(parameter W = 16);\n"
              "  static function logic [W-1:0] add(\n"
              "      input logic [W-1:0] a,\n"
              "      input logic [W-1:0] b);\n"
              "    return a + b;\n"
              "  endfunction\n"
              "endclass\n"));
}

// §13.8: Chained call — result of parameterized call used as argument.
TEST(ParserSection13, Sec13_8_ChainedParameterizedCalls) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] a, b, c;\n"
              "  assign c = Arith#(8)::add(a, Arith#(8)::add(a, b));\n"
              "endmodule\n"));
}

// §13.8: Parameterized class with no default parameter value.
TEST(ParserSection13, Sec13_8_NoDefaultParam) {
  auto r = Parse(
      "virtual class Shifter#(parameter int AMOUNT);\n"
      "  static function logic [31:0] left(input logic [31:0] val);\n"
      "    return val << AMOUNT;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes[0]->params.size(), 1u);
}

// §13.8: Specialized call with explicit parameter (no default).
TEST(ParserSection13, Sec13_8_ExplicitParamSpecialization) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [31:0] d, r;\n"
              "  assign r = Shifter#(4)::left(d);\n"
              "endmodule\n"));
}

// §13.8: Parameterized class with parameter used in local variable.
TEST(ParserSection13, Sec13_8_ParamInLocalVar) {
  EXPECT_TRUE(
      ParseOk("virtual class BitOps#(parameter W = 8);\n"
              "  static function logic [W-1:0] invert(input logic [W-1:0] x);\n"
              "    logic [W-1:0] mask;\n"
              "    mask = '1;\n"
              "    return x ^ mask;\n"
              "  endfunction\n"
              "endclass\n"));
}

// §13.8: Parameterized class extending another class.
TEST(ParserSection13, Sec13_8_ClassExtends) {
  EXPECT_TRUE(
      ParseOk("class Base;\n"
              "  virtual function void display();\n"
              "  endfunction\n"
              "endclass\n"
              "virtual class Derived#(parameter N = 1) extends Base;\n"
              "  static function int count();\n"
              "    return N;\n"
              "  endfunction\n"
              "endclass\n"));
}

// §13.8: Parameterized class with for loop using parameter as bound.
TEST(ParserSection13, Sec13_8_ForLoopWithParamBound) {
  EXPECT_TRUE(
      ParseOk("virtual class Popcount#(parameter W = 8);\n"
              "  static function int count_ones(input logic [W-1:0] val);\n"
              "    int cnt;\n"
              "    cnt = 0;\n"
              "    for (int i = 0; i < W; i++) begin\n"
              "      if (val[i]) cnt = cnt + 1;\n"
              "    end\n"
              "    return cnt;\n"
              "  endfunction\n"
              "endclass\n"));
}

// §13.8: Calling parameterized task from initial block.
TEST(ParserSection13, Sec13_8_CallParamTaskFromInitial) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial Utils#(16)::report();\n"
              "endmodule\n"));
}

// §13.8: Parameter with string type default.
TEST(ParserSection13, Sec13_8_StringTypeParam) {
  EXPECT_TRUE(
      ParseOk("virtual class Logger#(parameter string PREFIX = \"LOG\");\n"
              "  static task info(string msg);\n"
              "    $display(\"%s: %s\", PREFIX, msg);\n"
              "  endtask\n"
              "endclass\n"));
}

// §13.8: Return type uses parameter.
TEST(ParserSection13, Sec13_8_ReturnTypeUsesParam) {
  EXPECT_TRUE(
      ParseOk("virtual class Pack#(parameter W = 8);\n"
              "  static function logic [2*W-1:0] double(\n"
              "      input logic [W-1:0] x);\n"
              "    return {x, x};\n"
              "  endfunction\n"
              "endclass\n"));
}

// §13.8: Parameterized class with multiple methods calling each other.
TEST(ParserSection13, Sec13_8_MethodsCallEachOther) {
  EXPECT_TRUE(
      ParseOk("virtual class Math#(parameter W = 32);\n"
              "  static function logic [W-1:0] abs_val(\n"
              "      input logic signed [W-1:0] x);\n"
              "    return negate(x);\n"
              "  endfunction\n"
              "  static function logic [W-1:0] negate(\n"
              "      input logic signed [W-1:0] x);\n"
              "    return -x;\n"
              "  endfunction\n"
              "endclass\n"));
}

// §13.8: Assign result of parameterized call to variable.
TEST(ParserSection13, Sec13_8_AssignParamCallResult) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int result;\n"
              "  initial begin\n"
              "    result = Popcount#(32)::count_ones(32'hDEAD_BEEF);\n"
              "  end\n"
              "endmodule\n"));
}

// §13.8: Parameterized class scope in conditional expression.
TEST(ParserSection13, Sec13_8_ParamCallInTernary) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic [7:0] x, y;\n"
              "  logic sel;\n"
              "  assign y = sel ? C#(8)::ENCODER_f(x) : '0;\n"
              "endmodule\n"));
}

// §13.8: Virtual class with only a static task (no function).
TEST(ParserSection13, Sec13_8_OnlyStaticTask) {
  auto r = Parse(
      "virtual class Printer#(parameter int ID = 0);\n"
      "  static task print();\n"
      "    $display(\"ID=%0d\", ID);\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_virtual);
}

// §13.8: Parameter of type int explicitly typed.
TEST(ParserSection13, Sec13_8_ExplicitlyTypedParam) {
  auto r = Parse(
      "virtual class Buffer#(parameter int SIZE = 256);\n"
      "  static function int capacity();\n"
      "    return SIZE;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
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
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_EQ(r.cu->modules.size(), 1u);
  ASSERT_EQ(item->clocking_event.size(), 1u);
  ASSERT_EQ(item->clocking_signals.size(), 1u);

  // Validate properties, event, and signal via loop.
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
  ModuleItem* item = nullptr;
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
  ModuleItem* item = nullptr;
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
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));

  VerifyClockingSignalDirections(item, {
                                           {Direction::kInput, "data_in"},
                                           {Direction::kOutput, "data_out"},
                                           {Direction::kInout, "bidir"},
                                       });
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
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
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
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
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
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));

  const char* const kExpectedNames[] = {"data", "ready", "enable"};
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
  auto* item = FindClockingBlock(r);
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
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  auto& sig = item->clocking_signals[0];
  EXPECT_EQ(sig.direction, Direction::kInout);
  EXPECT_EQ(sig.name, "cmd");

  const void* const kSkewPtrs[] = {sig.skew_delay, sig.out_skew_delay};
  for (const auto* p : kSkewPtrs) {
    EXPECT_NE(p, nullptr);
  }
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
  auto* item = FindClockingBlock(r);
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
  auto* item = FindClockingBlock(r);
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
  auto* cb1 = FindClockingBlock(r, 0);
  auto* cb2 = FindClockingBlock(r, 1);
  ASSERT_NE(cb1, nullptr);
  ASSERT_NE(cb2, nullptr);
  EXPECT_EQ(cb1->name, "cd1");
  EXPECT_EQ(cb2->name, "cd2");
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
  ModuleItem* item = nullptr;
  ASSERT_NO_FATAL_FAILURE(GetClockingBlock(r, item));
  EXPECT_EQ(item->kind, ModuleItemKind::kClockingBlock);
  EXPECT_EQ(item->name, "bus");
  ASSERT_EQ(item->clocking_event.size(), 1u);
  EXPECT_EQ(item->clocking_event[0].edge, Edge::kPosedge);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
  EXPECT_EQ(item->clocking_signals[0].direction, Direction::kInput);
  EXPECT_EQ(item->clocking_signals[0].name, "addr");
}

}  // namespace
