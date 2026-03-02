// §35.5.4: Import declarations

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// dpi_import_export ::=
//   import dpi_spec_string [dpi_function_import_property] [c_identifier =]
//     dpi_function_proto ;
//   | import dpi_spec_string [dpi_task_import_property] [c_identifier =]
//     dpi_task_proto ;
//   | export dpi_spec_string [c_identifier =] function function_identifier ;
//   | export dpi_spec_string [c_identifier =] task task_identifier ;
// ---------------------------------------------------------------------------
TEST(ParserA26, DpiImportFunction) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_add(input int a, input int b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(item->name, "c_add");
  EXPECT_FALSE(item->dpi_is_task);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
  ASSERT_EQ(item->func_args.size(), 2u);
}

TEST(ParserA26, DpiImportTask) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" task c_do_work(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiImport);
  EXPECT_TRUE(item->dpi_is_task);
  EXPECT_EQ(item->name, "c_do_work");
}

// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------
TEST(ParserA26, DpiSpecStringDpiC) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void foo();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kDpiImport);
}

TEST(ParserA26, DpiSpecStringDpi) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI\" function void foo();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kDpiImport);
}

// ---------------------------------------------------------------------------
// dpi_function_import_property ::= context | pure
// ---------------------------------------------------------------------------
TEST(ParserA26, DpiFunctionImportPure) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" pure function int pure_add(input int a, input int "
      "b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->dpi_is_pure);
  EXPECT_FALSE(item->dpi_is_context);
}

TEST(ParserA26, DpiFunctionImportContext) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" context function void ctx_func();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->dpi_is_context);
  EXPECT_FALSE(item->dpi_is_pure);
}

// ---------------------------------------------------------------------------
// dpi_task_import_property ::= context
// ---------------------------------------------------------------------------
TEST(ParserA26, DpiTaskImportContext) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" context task ctx_task(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->dpi_is_context);
  EXPECT_TRUE(item->dpi_is_task);
}

// ---------------------------------------------------------------------------
// dpi_import_export: c_identifier = alias
// ---------------------------------------------------------------------------
TEST(ParserA26, DpiImportWithCIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" c_my_func = function int my_func(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(item->dpi_c_name, "c_my_func");
  EXPECT_EQ(item->name, "my_func");
}

TEST(ParserA26, DpiImportTaskWithCIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" c_work = task do_work();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->dpi_c_name, "c_work");
  EXPECT_EQ(item->name, "do_work");
  EXPECT_TRUE(item->dpi_is_task);
}

TEST(ParserA26, DpiImportPureWithCIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" pure c_fn = function int fn(input int a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->dpi_is_pure);
  EXPECT_EQ(item->dpi_c_name, "c_fn");
  EXPECT_EQ(item->name, "fn");
}

// ---------------------------------------------------------------------------
// dpi_function_proto / dpi_task_proto — complex argument types
// ---------------------------------------------------------------------------
TEST(ParserA26, DpiFuncProtoNoArgs) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int get_value();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->func_args.empty());
}

TEST(ParserA26, DpiFuncProtoMultipleArgs) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int compute(\n"
      "    input int a, input int b, input int c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 3u);
}

TEST(ParserA26, DpiTaskProtoWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" task run_sim(\n"
      "    input int cycles, output int result);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->dpi_is_task);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
}

// =============================================================================
// Annex H/I - DPI C layer / svdpi.h
// =============================================================================
TEST_F(AnnexHParseTest, AnnexHDpiImportFunction) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_add(int a, int b);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "c_add");
  EXPECT_FALSE(items[0]->dpi_is_task);
  EXPECT_FALSE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_context);
}

TEST_F(AnnexHParseTest, AnnexHDpiImportWithCName) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" c_name = function void my_func();\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->dpi_c_name, "c_name");
  EXPECT_EQ(items[0]->name, "my_func");
  EXPECT_FALSE(items[0]->dpi_is_task);
}

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

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
// Annex H - DPI import task
// =============================================================================
TEST_F(AnnexHParseTest, AnnexHDpiImportTask) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" task c_wait(int cycles);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "c_wait");
  EXPECT_TRUE(items[0]->dpi_is_task);
  ASSERT_EQ(items[0]->func_args.size(), 1u);
  EXPECT_EQ(items[0]->func_args[0].name, "cycles");
}

// =============================================================================
// Annex H - DPI context import task with C name
// =============================================================================
TEST_F(AnnexHParseTest, AnnexHDpiContextTaskWithCName) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" context c_poll = task poll_hardware(int timeout);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->dpi_c_name, "c_poll");
  EXPECT_EQ(items[0]->name, "poll_hardware");
  EXPECT_TRUE(items[0]->dpi_is_context);
  EXPECT_TRUE(items[0]->dpi_is_task);
}

// =============================================================================
// Annex H - DPI import no-arg function
// =============================================================================
TEST_F(AnnexHParseTest, AnnexHDpiImportNoArgs) {
  // A DPI import with no argument list at all (valid per LRM).
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int get_seed;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "get_seed");
  EXPECT_TRUE(items[0]->func_args.empty());
}

// =============================================================================
// Annex J - Foreign language code inclusion
// =============================================================================
TEST_F(AnnexHParseTest, AnnexJDpiImportCoexistence) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_func();\n"
      "  logic [7:0] data;\n"
      "  assign data = 8'hFF;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kContAssign);
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

struct ConfigTest : ::testing::Test {
 protected:
  CompilationUnit* Parse(const std::string& src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  bool HasErrors() const { return diag_.HasErrors(); }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

struct ParseResult34 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult34 Parse(const std::string& src) {
  ParseResult34 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// =============================================================================
// §35.3 DPI-C import declarations
// =============================================================================
TEST_F(DpiParseTest, ImportFunction) {
  auto* unit = Parse(R"(
    module m;
      import "DPI-C" function int add(input int a, input int b);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "add");
  EXPECT_FALSE(items[0]->dpi_is_task);
  EXPECT_FALSE(items[0]->dpi_is_pure);
  EXPECT_FALSE(items[0]->dpi_is_context);
}

TEST_F(DpiParseTest, ImportTask) {
  auto* unit = Parse(R"(
    module m;
      import "DPI-C" task do_something();
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "do_something");
  EXPECT_TRUE(items[0]->dpi_is_task);
}

TEST_F(DpiParseTest, ImportWithCName) {
  auto* unit = Parse(R"(
    module m;
      import "DPI-C" c_add = function int add(input int a, input int b);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->dpi_c_name, "c_add");
  EXPECT_EQ(items[0]->name, "add");
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
// Annex H - DPI import with default argument values
// =============================================================================
TEST_F(AnnexHParseTest, AnnexHDpiImportDefaultArgs) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int compute(\n"
      "    int a,\n"
      "    int b = 0,\n"
      "    int c = 42\n"
      "  );\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  ASSERT_EQ(items[0]->func_args.size(), 3u);
  EXPECT_EQ(items[0]->func_args[0].default_value, nullptr);
  EXPECT_NE(items[0]->func_args[1].default_value, nullptr);
  EXPECT_NE(items[0]->func_args[2].default_value, nullptr);
}

}  // namespace
