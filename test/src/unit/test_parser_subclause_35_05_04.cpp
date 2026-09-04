#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_config.h"
#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "simulator/vpi.h"

using namespace delta;

namespace {

TEST(FunctionDeclParsing, DpiSpecStringDpiC) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void foo();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kDpiImport);
}

TEST(FunctionDeclParsing, DpiSpecStringDpi) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI\" function void foo();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kDpiImport);
}

TEST(FunctionDeclParsing, DpiFunctionImportPure) {
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

TEST(FunctionDeclParsing, DpiFunctionImportContext) {
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

TEST(FunctionDeclParsing, DpiTaskImportContext) {
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

// §35.5.4: the c_identifier of an import declaration names the foreign task
// and defaults to the task_identifier, so an explicit one is recorded beside
// the imported task's SystemVerilog name rather than replacing it. The annex
// A.2.6 file carries the production-level case, which checks the task flag and
// the c_identifier alone.
TEST(FunctionDeclParsing, DpiImportCIdentifierBesideTaskIdentifier) {
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

TEST(FunctionDeclParsing, DpiImportPureWithCIdentifier) {
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

TEST(FunctionDeclParsing, DpiFuncProtoNoArgs) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int get_value();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->func_args.empty());
}

TEST(FunctionDeclParsing, DpiFuncProtoMultipleArgs) {
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

TEST(FunctionDeclParsing, DpiTaskProtoWithArgs) {
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

TEST_F(DpiParseTest, DpiImportVoidFunctionWithCIdentifier) {
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

TEST_F(DpiParseTest, DpiImportTaskCapturesFormalArgName) {
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

TEST_F(DpiParseTest, DpiImportContextTaskWithCIdentifier) {
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

TEST_F(DpiParseTest, DpiImportFunctionOmittedParameterList) {
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

TEST_F(DpiParseTest, DpiImportCoexistsWithVarAndContAssign) {
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

TEST(DpiParsing, DpiImportVoidCallbackFunction) {
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

TEST(DpiParsing, DpiImportWithCNameForCallback) {
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

TEST(DpiParsing, MultipleDpiDeclarationsForVpiRegistration) {
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

TEST_F(DpiParseTest, DpiImportFunctionWithDefaultArgValues) {
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

TEST_F(DpiParseTest, MultipleDpiImportExportDeclsInOneModule) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_add(int a, int b);\n"
      "  import \"DPI-C\" pure function real c_sin(real x);\n"
      "  export \"DPI-C\" function sv_compute;\n"
      "  export \"DPI-C\" task sv_run;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 4u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "c_add");
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[1]->name, "c_sin");
  EXPECT_TRUE(items[1]->dpi_is_pure);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[2]->name, "sv_compute");
  EXPECT_FALSE(items[2]->dpi_is_task);
  EXPECT_EQ(items[3]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[3]->name, "sv_run");
  EXPECT_TRUE(items[3]->dpi_is_task);
}

TEST(FunctionDeclParsing, DpiSpecStringStoredOnImport) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void foo();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->items[0]->dpi_spec_string, "DPI-C");
}

TEST(FunctionDeclParsing, DpiSpecStringStoredOnExport) {
  auto r = Parse(
      "module m;\n"
      "  export \"DPI-C\" function sv_foo;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->items[0]->dpi_spec_string, "DPI-C");
}

TEST(FunctionDeclParsing, DpiSpecStringInvalidIsError) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>",
                         "module m;\n"
                         "  import \"DPI-Q\" function void foo();\n"
                         "endmodule\n");
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  EXPECT_TRUE(ReportedError(
      diag.Diagnostics(),
      "DPI specification string must be \"DPI-C\" or \"DPI\"", 2, "35.5.4"));
}

// §35.5.4: "Use of the string "DPI" shall generate a compile-time warning or
// error. The tool-generated message shall contain the following information",
// and it then lists two items: that "DPI" is deprecated and should be replaced
// with "DPI-C", and that use of the "DPI-C" string may require changes in the
// DPI application's C code. Both items are the requirement, so the report is
// named by its whole sentence. A warning count is satisfied by any warning the
// run happened to write, including one about something else entirely.
TEST(FunctionDeclParsing, DpiDeprecatedStringWarnsButParses) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI\" function void foo();\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(ReportedWarning(
      r.diags,
      "\"DPI\" is deprecated and should be replaced with \"DPI-C\"; use of the "
      "\"DPI-C\" string may require changes in the DPI application's C code",
      2, "35.5.4"));
}

TEST(FunctionDeclParsing, DpiCanonicalStringEmitsNoWarning) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>",
                         "module m;\n"
                         "  import \"DPI-C\" function void foo();\n"
                         "endmodule\n");
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  EXPECT_FALSE(diag.HasErrors());
  EXPECT_EQ(diag.WarningCount(), 0u);
}

TEST(FunctionDeclParsing, DpiImportRefArgumentIsError) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>",
                         "module m;\n"
                         "  import \"DPI-C\" function void f(ref int x);\n"
                         "endmodule\n");
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  EXPECT_TRUE(ReportedError(
      diag.Diagnostics(),
      "ref qualifier cannot be used in a DPI import declaration", 2, "35.5.4"));
}

// §35.5.4: the c_identifier carries the foreign-language linkage name and
// must conform to C identifier syntax. SystemVerilog tolerates `$` inside an
// identifier but C does not, so an SV-legal name like `foo$bar` must be
// rejected when supplied as the linkage name.
TEST(FunctionDeclParsing, DpiCIdentifierWithDollarIsError) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>",
                         "module m;\n"
                         "  import \"DPI-C\" foo$bar = function void f();\n"
                         "endmodule\n");
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  EXPECT_TRUE(ReportedError(
      diag.Diagnostics(), "DPI c_identifier must match [a-zA-Z_][a-zA-Z0-9_]*",
      2, "35.5.4"));
}

// §35.5.4: the C-identifier conformance rule applies to export declarations
// as well; the same parser-side check is reused on the export path.
TEST(FunctionDeclParsing, DpiExportCIdentifierWithDollarIsError) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>",
                         "module m;\n"
                         "  export \"DPI-C\" foo$bar = function sv_f;\n"
                         "endmodule\n");
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  EXPECT_TRUE(ReportedError(
      diag.Diagnostics(), "DPI c_identifier must match [a-zA-Z_][a-zA-Z0-9_]*",
      2, "35.5.4"));
}

// Syntax 35-1 in §35.5.4 writes every import declaration with `task` or
// `function` after the optional properties, so an import naming neither
// breaches §35.5.4. The report Parser::ParseDpiImport in
// src/parser/parser_dpi.cpp writes for it names `function`. The first report
// is this one: it is written before the parser goes on to read what follows as
// a return type and a name.
TEST(FunctionDeclParsing, DpiImportMissingFunctionKeywordNames35_5_4) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" foo(input int x);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'function'", 2, "35.5.4"));
}

// §35.5.4 attaches the deprecation to the dpi_spec_string itself, and both
// export alternatives of dpi_import_export in Syntax 35-1 are written with
// that same dpi_spec_string, so an export naming "DPI" draws the same report
// as an import does.
TEST(FunctionDeclParsing, DpiExportDeprecatedStringWarns) {
  auto r = Parse(
      "module m;\n"
      "  export \"DPI\" function f;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(ReportedWarning(
      r.diags,
      "\"DPI\" is deprecated and should be replaced with \"DPI-C\"; use of the "
      "\"DPI-C\" string may require changes in the DPI application's C code",
      2, "35.5.4"));
}

// §35.5.4: "If not provided, this defaults to the same identifier as the
// SystemVerilog subroutine name. In either case, this linkage name shall
// conform to C identifier syntax. An error shall occur if the c_identifier,
// either directly or indirectly, does not conform to these rules." §5.6 admits
// '$' after the first character of a simple identifier, so `foo$bar` is one
// SystemVerilog identifier; standing in for an absent c_identifier it is the
// linkage name, and it is the indirect breach the clause names.
TEST(FunctionDeclParsing, DpiImportDefaultedLinkageNameWithDollarIsError) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void foo$bar();\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "DPI linkage name 'foo$bar', defaulted from the "
                            "subroutine name, must match "
                            "[a-zA-Z_][a-zA-Z0-9_]*",
                            2, "35.5.4"));
}

// §35.5.4 states the c_identifier rule once for the whole of
// dpi_import_export, and both export alternatives in Syntax 35-1 write the
// c_identifier as optional, so an export that omits it defaults its linkage
// name from the exported subroutine's name and is held to the same rule.
TEST(FunctionDeclParsing, DpiExportDefaultedLinkageNameWithDollarIsError) {
  auto r = Parse(
      "module m;\n"
      "  export \"DPI-C\" function foo$bar;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "DPI linkage name 'foo$bar', defaulted from the "
                            "subroutine name, must match "
                            "[a-zA-Z_][a-zA-Z0-9_]*",
                            2, "35.5.4"));
}

// §35.5.4: "An error shall occur if the c_identifier, either directly or
// indirectly, does not conform to these rules." An escaped identifier is the
// other way a subroutine name reaches characters C forbids: §5.6.1 has
// LexEscapedIdentifier in src/lexer/lexer.cpp drop the leading backslash and
// the terminating white space, so the name recorded here is `my-task`, and the
// hyphen in it is what the rule rejects.
TEST(FunctionDeclParsing, DpiImportDefaultedLinkageNameFromEscapedNameIsError) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void \\my-task ();\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "DPI linkage name 'my-task', defaulted from the "
                            "subroutine name, must match "
                            "[a-zA-Z_][a-zA-Z0-9_]*",
                            2, "35.5.4"));
}

// §35.5.4: "The c_identifier provides the linkage name for this subroutine in
// the foreign language." The rule is about that linkage name and not about the
// SystemVerilog subroutine name, so a c_identifier written out conforms on its
// own and the SystemVerilog name beside it is free to hold a '$' §5.6 allows.
TEST(FunctionDeclParsing, DpiImportExplicitCIdentifierLeavesSvNameFree) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" foo_c = function void foo$bar();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->dpi_c_name, "foo_c");
  EXPECT_EQ(item->name, "foo$bar");
}

// Footnote 25 of Syntax 35-1 in §35.5.4: "The dynamic_override_specifiers
// shall only be legal on method declarations inside a non-interface class
// scope." An import declaration declares no class method, so `:initial` on one
// is illegal wherever the import is written.
TEST(FunctionDeclParsing, DpiImportFunctionDynamicOverrideSpecifierIsError) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function :initial void f();\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "dynamic_override_specifiers shall only be legal "
                            "on method declarations inside a non-interface "
                            "class scope",
                            2, "35.5.4"));
}

// Footnote 25 of Syntax 35-1 in §35.5.4 governs the task form as well:
// task_prototype is written "task [ dynamic_override_specifiers ]
// task_identifier", carrying the same footnote, and an imported task is no
// more a class method declaration than an imported function is.
TEST(FunctionDeclParsing, DpiImportTaskDynamicOverrideSpecifierIsError) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" task :final t();\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "dynamic_override_specifiers shall only be legal "
                            "on method declarations inside a non-interface "
                            "class scope",
                            2, "35.5.4"));
}

// §35.5.4: "Formal argument names are optional unless argument binding by name
// is needed." Neither formal below is named, and the import is still a
// complete declaration of two arguments.
TEST(FunctionDeclParsing, DpiImportUnnamedFormalsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(input int, output bit [7:0]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_TRUE(item->func_args[0].name.empty());
  EXPECT_TRUE(item->func_args[1].name.empty());
}

// §35.5.4: "A formal argument name is required to separate the packed and the
// unpacked dimensions of an array." The name `a` stands between the two
// bracket groups, so `[7:0]` closes the packed part of the type and `[0:3]`
// opens the unpacked part. The two ranges differ, so a formal that took both
// groups into one part could not report one packed and one unpacked dimension.
TEST(FunctionDeclParsing, DpiImportNamedFormalSeparatesPackedFromUnpacked) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(input bit [7:0] a [0:3]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  const auto& arg = item->func_args[0];
  EXPECT_EQ(arg.name, "a");
  EXPECT_NE(arg.data_type.packed_dim_left, nullptr);
  EXPECT_TRUE(arg.data_type.extra_packed_dims.empty());
  ASSERT_EQ(arg.unpacked_dims.size(), 1u);
  EXPECT_NE(arg.unpacked_dims[0], nullptr);
}

// §35.5.4 requires the name because the name is the only separator there is:
// with it left out of the same declaration, nothing stands between the two
// bracket groups and both belong to the packed part of the type. This is the
// reading that makes the sentence quoted above true.
TEST(FunctionDeclParsing, DpiImportUnnamedFormalKeepsBothGroupsPacked) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(input bit [7:0] [0:3]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  const auto& arg = item->func_args[0];
  EXPECT_TRUE(arg.name.empty());
  EXPECT_NE(arg.data_type.packed_dim_left, nullptr);
  ASSERT_EQ(arg.data_type.extra_packed_dims.size(), 1u);
  EXPECT_TRUE(arg.unpacked_dims.empty());
}

}  // namespace
