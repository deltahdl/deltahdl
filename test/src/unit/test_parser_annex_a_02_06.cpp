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

namespace {

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

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

RtlirDesign* Elaborate(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

}  // namespace

// =============================================================================
// A.2.6 Function declarations
// =============================================================================

// ---------------------------------------------------------------------------
// function_data_type_or_implicit ::=
//   data_type_or_void | implicit_data_type
// ---------------------------------------------------------------------------

TEST(ParserA26, FuncReturnTypeExplicitInt) {
  auto r = Parse(
      "module m;\n  function int foo(); return 0; endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->name, "foo");
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

TEST(ParserA26, FuncReturnTypeVoid) {
  auto r = Parse("module m;\n  function void bar(); endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

TEST(ParserA26, FuncReturnTypeImplicit) {
  auto r =
      Parse("module m;\n  function foo(); return 1; endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kImplicit);
}

TEST(ParserA26, FuncReturnTypeImplicitSigned) {
  auto r = Parse(
      "module m;\n  function signed [7:0] foo();\n"
      "    return 0;\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->return_type.is_signed);
}

TEST(ParserA26, FuncReturnTypeLogicPacked) {
  auto r = Parse(
      "module m;\n  function logic [3:0] baz();\n"
      "    return 4'b0;\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(item->return_type.packed_dim_left, nullptr);
  EXPECT_NE(item->return_type.packed_dim_right, nullptr);
}

// ---------------------------------------------------------------------------
// function_declaration ::=
//   function [ dynamic_override_specifiers ] [ lifetime ]
//     function_body_declaration
// ---------------------------------------------------------------------------

TEST(ParserA26, FuncLifetimeAutomatic) {
  auto r = Parse(
      "module m;\n  function automatic int foo();\n"
      "    return 1;\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
}

TEST(ParserA26, FuncLifetimeStatic) {
  auto r = Parse(
      "module m;\n  function static int foo();\n"
      "    return 1;\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_FALSE(item->is_automatic);
  EXPECT_TRUE(item->is_static);
}

TEST(ParserA26, FuncLifetimeDefault) {
  auto r = Parse(
      "module m;\n  function int foo();\n"
      "    return 1;\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_FALSE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
}

TEST(ParserA26, FuncDynamicOverrideInitial) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :initial int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA26, FuncDynamicOverrideExtends) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :extends int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA26, FuncDynamicOverrideFinal) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :final int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA26, FuncDynamicOverrideInitialFinal) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :initial :final int foo();\n"
      "    return 0;\n  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA26, FuncDynamicOverrideExtendsFinal) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :extends :final int foo();\n"
      "    return 0;\n  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// function_body_declaration (new-style ports)
// ---------------------------------------------------------------------------

TEST(ParserA26, FuncBodyNewStyleEmptyPorts) {
  auto r =
      Parse("module m;\n  function void foo();\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->func_args.empty());
}

TEST(ParserA26, FuncBodyNewStyleWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  function int add(input int a, input int b);\n"
      "    return a + b;\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].name, "b");
}

TEST(ParserA26, FuncBodyNewStyleWithDefaultValue) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(input int x = 5);\n"
      "    return x;\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_NE(item->func_args[0].default_value, nullptr);
}

TEST(ParserA26, FuncBodyNewStyleMultipleDirections) {
  auto r = Parse(
      "module m;\n"
      "  function void xfer(input int a, output int b, inout int c, ref int "
      "d);\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 4u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(item->func_args[2].direction, Direction::kInout);
  EXPECT_EQ(item->func_args[3].direction, Direction::kRef);
}

TEST(ParserA26, FuncBodyNewStyleConstRef) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(const ref int x);\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

TEST(ParserA26, FuncBodyNewStyleStickyDirection) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(input int a, int b, int c);\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 3u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[2].direction, Direction::kInput);
}

TEST(ParserA26, FuncBodyWithBlockItemDecl) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(input int x);\n"
      "    int temp;\n"
      "    temp = x + 1;\n"
      "    return temp;\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_GE(item->func_body_stmts.size(), 1u);
}

TEST(ParserA26, FuncBodyWithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  function void foo();\n"
      "  endfunction : foo\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "foo");
}

// ---------------------------------------------------------------------------
// function_body_declaration (old-style ports)
// ---------------------------------------------------------------------------

TEST(ParserA26, FuncBodyOldStylePorts) {
  auto r = Parse(
      "module m;\n"
      "  function int foo;\n"
      "    input int a;\n"
      "    input int b;\n"
      "    foo = a + b;\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].name, "b");
}

TEST(ParserA26, FuncBodyOldStyleOutputPort) {
  auto r = Parse(
      "module m;\n"
      "  function void xfer;\n"
      "    input int a;\n"
      "    output int b;\n"
      "    b = a;\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
}

// ---------------------------------------------------------------------------
// function_body_declaration (scope qualifiers)
// ---------------------------------------------------------------------------

TEST(ParserA26, FuncBodyClassScope) {
  auto r = Parse(
      "class C;\n"
      "  extern function int foo();\n"
      "endclass\n"
      "function int C::foo();\n"
      "  return 42;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA26, FuncBodyConstructorNew) {
  auto r = Parse(
      "class C;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA26, FuncBodyConstructorNewEndLabel) {
  auto r = Parse(
      "class C;\n"
      "  function new(int x);\n"
      "  endfunction : new\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA26, FuncBodyOutOfBlockConstructor) {
  auto r = Parse(
      "class C;\n"
      "  extern function new();\n"
      "endclass\n"
      "function C::new();\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// ---------------------------------------------------------------------------
// function_prototype ::=
//   function [ dynamic_override_specifiers ] data_type_or_void
//     function_identifier [ ( [ tf_port_list ] ) ]
// ---------------------------------------------------------------------------

TEST(ParserA26, FuncPrototypeExtern) {
  auto r = Parse(
      "module m;\n"
      "  extern function int foo(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_extern);
  EXPECT_EQ(item->name, "foo");
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

TEST(ParserA26, FuncPrototypeExternVoid) {
  auto r = Parse(
      "module m;\n"
      "  extern function void bar();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_extern);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

TEST(ParserA26, FuncPrototypePureVirtual) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual function int compute(input int x);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

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

TEST(ParserA26, DpiImportFunctionVoid) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void c_print(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
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
// dpi_spec_string ::= "DPI-C" | "DPI"
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
// dpi_import_export: export variants
// ---------------------------------------------------------------------------

TEST(ParserA26, DpiExportFunction) {
  auto r = Parse(
      "module m;\n"
      "  function void sv_func(); endfunction\n"
      "  export \"DPI-C\" function sv_func;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(item->name, "sv_func");
  EXPECT_FALSE(item->dpi_is_task);
}

TEST(ParserA26, DpiExportTask) {
  auto r = Parse(
      "module m;\n"
      "  task sv_task(); endtask\n"
      "  export \"DPI-C\" task sv_task;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiExport);
  EXPECT_TRUE(item->dpi_is_task);
  EXPECT_EQ(item->name, "sv_task");
}

TEST(ParserA26, DpiExportWithCIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  function void sv_func(); endfunction\n"
      "  export \"DPI-C\" c_name = function sv_func;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[1];
  EXPECT_EQ(item->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(item->dpi_c_name, "c_name");
  EXPECT_EQ(item->name, "sv_func");
}

TEST(ParserA26, DpiExportDpiLegacy) {
  auto r = Parse(
      "module m;\n"
      "  function void sv_func(); endfunction\n"
      "  export \"DPI\" function sv_func;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[1]->kind, ModuleItemKind::kDpiExport);
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

// ---------------------------------------------------------------------------
// function_body_declaration: argument unpacked dimensions (§13.4)
// ---------------------------------------------------------------------------

TEST(ParserA26, FuncArgUnpackedDim) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(input int arr [4]);\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].unpacked_dims.size(), 1u);
}

// ---------------------------------------------------------------------------
// Elaboration: function declaration within module
// ---------------------------------------------------------------------------

TEST(ParserA26, ElabFunctionDeclInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function int add(input int a, input int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ParserA26, ElabFunctionAutomaticLifetime) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  function automatic int fact(input int n);\n"
      "    if (n <= 1) return 1;\n"
      "    return n;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}
