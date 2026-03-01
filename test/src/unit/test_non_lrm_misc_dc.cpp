// Non-LRM tests

#include "fixture_program.h"
#include "fixture_simulator.h"

using namespace delta;

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

static bool ParseOk38(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

struct ParseResult40 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult40 Parse(const std::string& src) {
  ParseResult40 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

TEST(ParserSection38, DpiImportContextCallbackWithArgs) {
  // Context function with arguments typical for VPI callback registration
  auto r = Parse(R"(
    module m;
      import "DPI-C" context function int register_cb_wrapper(
        input int reason, input string user_data
      );
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_TRUE(items[0]->dpi_is_context);
  EXPECT_EQ(items[0]->name, "register_cb_wrapper");
}

TEST(ParserSection38, DpiImportWithCNameForCallback) {
  // C-name mapping for VPI registration function linkage
  auto r = Parse(R"(
    module m;
      import "DPI-C" vpi_cb_rtn =
        function void cb_value_change(input int reason);
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->dpi_c_name, "vpi_cb_rtn");
  EXPECT_EQ(items[0]->name, "cb_value_change");
}

TEST(ParserSection38, DpiImportPureFunctionForSizetf) {
  // Pure function import modeling the sizetf callback (no side effects)
  auto r = Parse(R"(
    module m;
      import "DPI-C" pure function int my_sizetf(input string data);
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_TRUE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_context);
}

// =============================================================================
// LRM section 38.37 -- vpi_register_systf: DPI-C exports for system tasks
// These tests verify DPI-C export declarations modeling the callback
// registration pattern used by vpi_register_systf().
// =============================================================================
TEST(ParserSection38, DpiExportFunctionForCalltf) {
  // Export an SV function for C-side systf registration
  auto r = Parse(R"(
    module m;
      export "DPI-C" function calltf_routine;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[0]->name, "calltf_routine");
  EXPECT_FALSE(items[0]->dpi_is_task);
}

TEST(ParserSection38, DpiExportTaskForSystf) {
  // Export a task for use as a systf callback handler
  auto r = Parse(R"(
    module m;
      export "DPI-C" task systf_handler;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_TRUE(items[0]->dpi_is_task);
}

TEST(ParserSection38, DpiExportWithCNameForSystf) {
  // Export with explicit C-side name for systf registration
  auto r = Parse(R"(
    module m;
      export "DPI-C" my_c_calltf = function sv_calltf;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->dpi_c_name, "my_c_calltf");
  EXPECT_EQ(items[0]->name, "sv_calltf");
}

TEST(ParserSection38, MultipleDpiDeclarationsForVpiRegistration) {
  // Multiple import/export declarations modeling a complete VPI registration
  // set
  EXPECT_TRUE(ParseOk38(R"(
    module m;
      import "DPI-C" context function int calltf(input string data);
      import "DPI-C" context function int compiletf(input string data);
      import "DPI-C" pure function int sizetf(input string data);
      export "DPI-C" function sv_calltf_impl;
      export "DPI-C" task sv_task_impl;
    endmodule
  )"));
}

// =============================================================================
// LRM section 39.4.1 -- Placing assertion system callbacks
// These system tasks control assertion processing at the system level:
// $assertOn, $assertOff, $assertKill
// =============================================================================
TEST(ParserSection39, AssertOnNoArgs) {
  // $assertOn with no arguments enables all assertions
  auto r = Parse(R"(
    module m;
      initial $asserton;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection39, AssertOffNoArgs) {
  // $assertOff with no arguments disables all assertions
  auto r = Parse(R"(
    module m;
      initial $assertoff;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection39, AssertKillNoArgs) {
  // $assertKill kills all active assertion attempts
  auto r = Parse(R"(
    module m;
      initial $assertkill;
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection39, AssertOnWithLevelArg) {
  // $asserton with levels_arg controls depth of hierarchy
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $asserton(0);
    endmodule
  )"));
}

TEST(ParserSection39, AssertOffWithLevelAndModuleArgs) {
  // $assertoff with levels and list of modules/instances
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $assertoff(0, m);
    endmodule
  )"));
}

// =============================================================================
// LRM section 39.4.2 -- Placing assertion callbacks
// These tests verify assertion-related syntax that enables placement of
// callbacks on assertion statements (assert, assume, cover properties).
// =============================================================================
TEST(ParserSection39, AssertPropertyStatement) {
  // assert property is the target of assertion callbacks
  auto r = Parse(R"(
    module m;
      logic clk, a, b;
      assert property (@(posedge clk) a |-> b);
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  // Find the assert property item
  bool found_assert = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAssertProperty) {
      found_assert = true;
    }
  }
  EXPECT_TRUE(found_assert);
}

TEST(ParserSection39, AssumePropertyStatement) {
  // assume property can also have callbacks placed on it
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, req, gnt;
      assume property (@(posedge clk) req |-> ##[1:3] gnt);
    endmodule
  )"));
}

TEST(ParserSection39, CoverPropertyStatement) {
  // cover property is used for coverage callbacks
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, a, b;
      cover property (@(posedge clk) a ##1 b);
    endmodule
  )"));
}

// =============================================================================
// LRM section 39.5.2 -- Assertion control via system tasks
// The assertion control functions $assertcontrol and related tasks allow
// runtime control over assertion evaluation.
// =============================================================================
TEST(ParserSection39, AssertControlSystemTask) {
  // $assertcontrol enables runtime assertion control
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $assertcontrol(3);
    endmodule
  )"));
}

TEST(ParserSection39, AssertControlWithMultipleArgs) {
  // $assertcontrol with control_type and assertion_type arguments
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $assertcontrol(3, 1);
    endmodule
  )"));
}

TEST(ParserSection39, AssertPassStepAndFailStep) {
  // $assertpasson / $assertpassoff control pass action execution
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial begin
        $assertpasson;
        $assertpassoff;
      end
    endmodule
  )"));
}

TEST(ParserSection39, AssertionControlInAlwaysBlock) {
  // Assertion control tasks in always blocks
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, reset;
      always @(posedge clk) begin
        if (reset)
          $assertoff(0, m);
        else
          $asserton(0, m);
      end
    endmodule
  )"));
}

TEST(ParserSection39, AssertionControlSequence) {
  // Complete assertion control sequence: off, kill, on
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial begin
        $assertoff;
        $assertkill;
        #100;
        $asserton;
      end
    endmodule
  )"));
}

TEST(ParserSection40, CoverageGetSystemCall) {
  // $coverage_get returns current coverage count
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial begin
        int val;
        val = $coverage_get(0, 0);
      end
    endmodule
  )"));
}

TEST(ParserSection40, CoverageMergeSystemCall) {
  // $coverage_merge merges coverage databases
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $coverage_merge("database.ucdb");
    endmodule
  )"));
}

TEST(ParserSection40, CoverageSaveSystemCall) {
  // $coverage_save saves coverage data to file
  EXPECT_TRUE(ParseOk(R"(
    module m;
      initial $coverage_save("coverage.ucdb");
    endmodule
  )"));
}

// =============================================================================
// LRM section 40.5.2 -- Coverage with assertion and covergroup constructs
// The VPI coverage API queries are applied to assertion handles and
// covergroup instances. These tests verify the parser handles the
// constructs that coverage queries operate on.
// =============================================================================
TEST(ParserSection40, CovergroupWithCoverpoint) {
  // Covergroup with coverpoint -- target of vpi_get(vpiCovered, ...)
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic [2:0] addr;
      covergroup cg @(addr);
        coverpoint addr;
      endgroup
    endmodule
  )"));
}

TEST(ParserSection40, CoverPropertyForAssertionCoverage) {
  // cover property -- target of vpiAssertAttemptCovered/vpiAssertSuccessCovered
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, a, b;
      cover property (@(posedge clk) a |-> ##[1:3] b);
    endmodule
  )"));
}

TEST(ParserSection40, CoverageControlInAlwaysBlock) {
  // Coverage control calls within procedural context
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic clk, reset;
      always @(posedge clk) begin
        if (reset) begin
          $coverage_control(2, 0, 0);
        end
      end
    endmodule
  )"));
}

// §10.9: named assignment pattern elaborates for struct init
TEST(ElabA60701, StructNamedPatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{a: 8'd1, b: 8'd2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

// Clocking block with assertion_item_declaration elaborates
TEST(ElabA611, AssertionItemDeclElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "    property p;\n"
      "      data;\n"
      "    endproperty\n"
      "    sequence s;\n"
      "      data;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
