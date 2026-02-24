// §35.5.4: Import declarations

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

RtlirDesign *Elaborate(const std::string &src, ElabFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

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
  auto *item = r.cu->modules[0]->items[0];
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
  auto *item = r.cu->modules[0]->items[0];
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
  auto *item = r.cu->modules[0]->items[0];
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
  auto *item = r.cu->modules[0]->items[0];
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
  auto *item = r.cu->modules[0]->items[0];
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
  auto *item = r.cu->modules[0]->items[0];
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
  auto *item = r.cu->modules[0]->items[0];
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
  auto *item = r.cu->modules[0]->items[0];
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
  auto *item = r.cu->modules[0]->items[0];
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
  auto *item = r.cu->modules[0]->items[0];
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
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->dpi_is_task);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
}

}  // namespace
