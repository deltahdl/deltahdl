// Tests for LRM section 38.36, 38.37 -- VPI callback registration, DPI-C
// linkage, and VPI-related system functions

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

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
  bool found_dpi = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kDpiImport) {
      found_dpi = true;
      EXPECT_EQ(item->name, "set_value");
      EXPECT_TRUE(item->dpi_is_context);
    }
  }
  EXPECT_TRUE(found_dpi);
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

TEST(ParserSection38, DpiImportContextTask) {
  // Context task import (for callbacks that need simulator context)
  auto r = Parse(R"(
    module m;
      import "DPI-C" context task vpi_sim_callback();
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_TRUE(items[0]->dpi_is_context);
  EXPECT_TRUE(items[0]->dpi_is_task);
}
