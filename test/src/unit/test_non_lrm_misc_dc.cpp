// Non-LRM tests

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {


TEST_F(DpiParseTest, ExportTask) {
  auto* unit = Parse(R"(
    module m;
      export "DPI-C" task my_task;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[0]->name, "my_task");
  EXPECT_TRUE(items[0]->dpi_is_task);
}

TEST_F(DpiParseTest, ExportWithCName) {
  auto* unit = Parse(R"(
    module m;
      export "DPI-C" c_func = function sv_func;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[0]->dpi_c_name, "c_func");
  EXPECT_EQ(items[0]->name, "sv_func");
}

// =============================================================================
// Coexistence with package imports/exports
// =============================================================================
TEST_F(DpiParseTest, PackageImportStillWorks) {
  auto* unit = Parse(R"(
    module m;
      import pkg::*;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kImportDecl);
}

TEST_F(DpiParseTest, DpiImportCoexistsWithPackageImport) {
  auto* unit = Parse(R"(
    module m;
      import pkg::foo;
      import "DPI-C" function int c_func();
      export "DPI-C" function sv_func;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kDpiExport);
}

// =============================================================================
// §35.2.1 Attributes on modules/instances
// =============================================================================
TEST_F(DpiParseTest, AttributeOnModuleDefinition) {
  auto* unit = Parse(R"(
    (* optimize_power *)
    module m;
      wire a;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->modules[0]->name, "m");
}

TEST_F(DpiParseTest, AttributeOnModuleInstantiation) {
  auto* unit = Parse(R"(
    module m;
      (* dont_touch *)
      sub u1(.a(x));
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kModuleInst);
  ASSERT_FALSE(items[0]->attrs.empty());
  EXPECT_EQ(items[0]->attrs[0].name, "dont_touch");
}

TEST_F(DpiParseTest, AttributeWithValueOnInstance) {
  auto* unit = Parse(R"(
    module m;
      (* optimize_power = 0 *)
      sub u1(.a(x));
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_FALSE(items[0]->attrs.empty());
  EXPECT_EQ(items[0]->attrs[0].name, "optimize_power");
  EXPECT_NE(items[0]->attrs[0].value, nullptr);
}

// =============================================================================
// §35.5 Attribute compatibility (multiple attributes)
// =============================================================================
TEST_F(DpiParseTest, MultipleAttributesOnDecl) {
  auto* unit = Parse(R"(
    module m;
      (* full_case, parallel_case *)
      wire a;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_GE(items[0]->attrs.size(), 2u);
  EXPECT_EQ(items[0]->attrs[0].name, "full_case");
  EXPECT_EQ(items[0]->attrs[1].name, "parallel_case");
}

TEST_F(DpiParseTest, AttributeWithAndWithoutValue) {
  auto* unit = Parse(R"(
    module m;
      (* full_case, parallel_case = 1 *)
      wire a;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_GE(items[0]->attrs.size(), 2u);
  EXPECT_EQ(items[0]->attrs[0].value, nullptr);
  EXPECT_NE(items[0]->attrs[1].value, nullptr);
}

struct ApiParseTest : ::testing::Test {
 protected:
  CompilationUnit* Parse(const std::string& src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

// =============================================================================
// §39 Assertion control system functions
// =============================================================================
TEST_F(ApiParseTest, AssertOnSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $assertOn;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, AssertOffSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $assertOff;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, AssertKillSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $assertKill;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

// =============================================================================
// §40 Coverage control system functions
// =============================================================================
TEST_F(ApiParseTest, CoverageControlSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $coverage_control(1, 2, 3);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, CoverageGetMaxSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial begin
        int x;
        x = $coverage_get_max(0, 0);
      end
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

// =============================================================================
// §41 Data read API / General system functions
// =============================================================================
TEST_F(ApiParseTest, SdfAnnotateSystemCall) {
  auto* unit = Parse(R"(
    module m;
      initial $sdf_annotate("timing.sdf");
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, ReadmemhSystemCall) {
  auto* unit = Parse(R"(
    module m;
      logic [7:0] mem [0:255];
      initial $readmemh("data.hex", mem);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, ReadmembSystemCall) {
  auto* unit = Parse(R"(
    module m;
      logic [7:0] mem [0:255];
      initial $readmemb("data.bin", mem);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, WritememhSystemCall) {
  auto* unit = Parse(R"(
    module m;
      logic [7:0] mem [0:255];
      initial $writememh("data.hex", mem);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(ApiParseTest, MultipleApiCallsInModule) {
  auto* unit = Parse(R"(
    module m;
      initial begin
        $assertOn;
        $coverage_control(1, 0, 0);
        $readmemh("data.hex", mem);
      end
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  ASSERT_FALSE(unit->modules[0]->items.empty());
}

// =============================================================================
// §36.3 Configuration rules (config ... endconfig)
// =============================================================================
TEST_F(ApiParseTest, BasicConfigDecl) {
  auto* unit = Parse(R"(
    config cfg1;
      design rtlLib.top;
      default liblist rtlLib;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg1");
  ASSERT_EQ(unit->configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(unit->configs[0]->design_cells[0].first, "rtlLib");
  EXPECT_EQ(unit->configs[0]->design_cells[0].second, "top");
}

// =============================================================================
// §36.9.1 Config library (cell clause)
// =============================================================================
TEST_F(ApiParseTest, ConfigCellClauseLiblist) {
  auto* unit = Parse(R"(
    config cfg1;
      design lib1.top;
      default liblist lib1;
      cell adder liblist lib2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto* cell_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(cell_rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(cell_rule->cell_name, "adder");
  ASSERT_EQ(cell_rule->liblist.size(), 1u);
  EXPECT_EQ(cell_rule->liblist[0], "lib2");
}

TEST_F(ApiParseTest, ConfigCellClauseWithLib) {
  auto* unit = Parse(R"(
    config cfg1;
      design lib1.top;
      default liblist lib1;
      cell gateLib.adder use rtlLib.adder;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto* cell_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(cell_rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(cell_rule->cell_lib, "gateLib");
  EXPECT_EQ(cell_rule->cell_name, "adder");
  EXPECT_EQ(cell_rule->use_lib, "rtlLib");
  EXPECT_EQ(cell_rule->use_cell, "adder");
}

// =============================================================================
// §36.9.2 Config instance clause
// =============================================================================
TEST_F(ApiParseTest, ConfigInstanceClauseLiblist) {
  auto* unit = Parse(R"(
    config cfg1;
      design rtlLib.top;
      default liblist rtlLib;
      instance top.a2 liblist gateLib;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto* inst_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(inst_rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(inst_rule->inst_path, "top.a2");
  ASSERT_EQ(inst_rule->liblist.size(), 1u);
  EXPECT_EQ(inst_rule->liblist[0], "gateLib");
}

TEST_F(ApiParseTest, ConfigInstanceClauseUse) {
  auto* unit = Parse(R"(
    config cfg1;
      design lib1.top;
      default liblist lib1;
      instance top.u1 use lib2.cell_impl;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto* inst_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(inst_rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(inst_rule->inst_path, "top.u1");
  EXPECT_EQ(inst_rule->use_lib, "lib2");
  EXPECT_EQ(inst_rule->use_cell, "cell_impl");
}

TEST_F(ApiParseTest, ConfigInstanceClauseUseConfig) {
  auto* unit = Parse(R"(
    config cfg1;
      design lib1.top;
      default liblist lib1;
      instance top.bot use lib1.bot:config;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  ASSERT_GE(unit->configs[0]->rules.size(), 2u);
  auto* inst_rule = unit->configs[0]->rules[1];
  EXPECT_EQ(inst_rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(inst_rule->use_cell, "bot");
  EXPECT_TRUE(inst_rule->use_config);
}

struct ParseResult38 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult38 Parse(const std::string& src) {
  ParseResult38 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

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

static ModuleItem* FindItemByKind(ParseResult38& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

// =============================================================================
// LRM section 38.36 -- vpi_register_cb: DPI-C imports for VPI callbacks
// These tests verify that DPI-C import declarations with signatures typical
// of VPI callback routines parse correctly.
// =============================================================================
TEST(ParserSection38, VpiSystemCallDeposit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $deposit(sig, 1'b1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection38, VpiSystemCallForce) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    force sig = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection38, VpiSystemCallRelease) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    release sig;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection38, DpiImportForVpiAccess) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" context function void\n"
      "    set_value(input int handle, input int val);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* dpi = FindItemByKind(r, ModuleItemKind::kDpiImport);
  ASSERT_NE(dpi, nullptr);
  EXPECT_EQ(dpi->name, "set_value");
  EXPECT_TRUE(dpi->dpi_is_context);
}

// LRM section 38.36 -- vpi_register_cb callback function signatures
TEST(ParserSection38, DpiImportVoidCallbackFunction) {
  // Import a void function modeling a VPI callback routine
  auto r = Parse(R"(
    module m;
      import "DPI-C" function void my_callback();
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "my_callback");
  EXPECT_FALSE(items[0]->dpi_is_task);
}

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

struct ParseResult39 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult39 Parse(const std::string& src) {
  ParseResult39 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
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

struct ElabA60701Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabA60701Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// §10.9: named assignment pattern elaborates for struct init
TEST(ElabA60701, StructNamedPatternElaborates) {
  ElabA60701Fixture f;
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

struct ElabA611Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabA611Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

// Clocking block with assertion_item_declaration elaborates
TEST(ElabA611, AssertionItemDeclElaborates) {
  ElabA611Fixture f;
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

struct ElabA612Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabA612Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

}  // namespace
