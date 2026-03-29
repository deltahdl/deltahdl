#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(FunctionDeclParsing, FunctionDeclBasic) {
  auto r = Parse(
      "module m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstFunctionDecl(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "add");
  EXPECT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

TEST(FunctionDeclParsing, FunctionDeclLifetimeAutomatic) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int f(); return 0; endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstFunctionDecl(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
}

TEST(FunctionDeclParsing, FunctionDeclLifetimeStatic) {
  auto r = Parse(
      "module m;\n"
      "  function static int f(); return 0; endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstFunctionDecl(r);
  ASSERT_NE(item, nullptr);
  EXPECT_FALSE(item->is_automatic);
  EXPECT_TRUE(item->is_static);
}

TEST(FunctionDeclParsing, FunctionDeclVoidReturn) {
  auto r = Parse(
      "module m;\n"
      "  function void f(); endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstFunctionDecl(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

TEST(FunctionDeclParsing, FunctionOldStylePorts) {
  auto r = Parse(
      "module m;\n"
      "  function int f;\n"
      "    input int a;\n"
      "    input int b;\n"
      "    f = a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstFunctionDecl(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
}

TEST(FunctionDeclParsing, FunctionEndLabel) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function int f(); return 0; endfunction : f\n"
              "endmodule\n"));
}

TEST(FunctionDeclParsing, FunctionImplicitReturnType) {
  auto r = Parse(
      "module m;\n"
      "  function [7:0] f(); return 8'hFF; endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstFunctionDecl(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->return_type.packed_dim_left, nullptr);
  EXPECT_NE(item->return_type.packed_dim_right, nullptr);
}

TEST(FunctionDeclParsing, FunctionDynOverrideInitial) {
  EXPECT_TRUE(
      ParseOk("class c;\n"
              "  virtual function :initial void f(); endfunction\n"
              "endclass\n"));
}

TEST(FunctionDeclParsing, FunctionDynOverrideFinal) {
  EXPECT_TRUE(
      ParseOk("class c;\n"
              "  virtual function :final void f(); endfunction\n"
              "endclass\n"));
}

TEST(FunctionDeclParsing, FunctionDynOverrideExtends) {
  EXPECT_TRUE(
      ParseOk("class c;\n"
              "  virtual function :extends void f(); endfunction\n"
              "endclass\n"));
}

TEST(FunctionDeclParsing, DpiImportFunction) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_func(int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kDpiImport);
  ASSERT_NE(item, nullptr);
  EXPECT_FALSE(item->dpi_is_task);
}

TEST(FunctionDeclParsing, DpiImportTask) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" task c_task(int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kDpiImport);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->dpi_is_task);
}

TEST(FunctionDeclParsing, DpiImportPure) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" pure function int pure_func(int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kDpiImport);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->dpi_is_pure);
  EXPECT_FALSE(item->dpi_is_context);
}

TEST(FunctionDeclParsing, DpiImportContext) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" context function void ctx_func();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kDpiImport);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->dpi_is_context);
}

TEST(FunctionDeclParsing, DpiImportWithCIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" c_name = function void sv_func();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kDpiImport);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->dpi_c_name, "c_name");
}

TEST(FunctionDeclParsing, DpiExportFunction) {
  auto r = Parse(
      "module m;\n"
      "  function void my_func(); endfunction\n"
      "  export \"DPI-C\" function my_func;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kDpiExport);
  ASSERT_NE(item, nullptr);
  EXPECT_FALSE(item->dpi_is_task);
}

TEST(FunctionDeclParsing, DpiExportTask) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(); endtask\n"
      "  export \"DPI-C\" task my_task;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kDpiExport);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->dpi_is_task);
}

TEST(FunctionDeclParsing, DpiExportWithCIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  function void my_func(); endfunction\n"
      "  export \"DPI-C\" c_alias = function my_func;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kDpiExport);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->dpi_c_name, "c_alias");
}

TEST(FunctionDeclParsing, DpiSpecStringDPI) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  import \"DPI\" function void f();\n"
              "endmodule\n"));
}

TEST(FunctionDeclParsing, FunctionPrototypeNoArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  import \"DPI-C\" function void no_args;\n"
              "endmodule\n"));
}

TEST(FunctionDeclParsing, FunctionPrototypeEmptyParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  import \"DPI-C\" function void empty_args();\n"
              "endmodule\n"));
}

TEST(FunctionDeclParsing, FunctionBodyWithBlockItem) {
  auto r = Parse(
      "module m;\n"
      "  function int f(int x);\n"
      "    int temp;\n"
      "    temp = x * 2;\n"
      "    return temp;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstFunctionDecl(r);
  ASSERT_NE(item, nullptr);
  EXPECT_GE(item->func_body_stmts.size(), 2u);
}

// --- function_declaration: no lifetime (default) ---

TEST(FunctionDeclParsing, FunctionDeclNoLifetime) {
  auto r = Parse(
      "module m;\n"
      "  function int f(); return 0; endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstFunctionDecl(r);
  ASSERT_NE(item, nullptr);
  EXPECT_FALSE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
}

// --- function_body_declaration: interface_identifier form ---

TEST(FunctionDeclParsing, FunctionBodyWithInterfaceScope) {
  EXPECT_TRUE(ParseOk(
      "interface ifc;\n"
      "  function int f(); return 0; endfunction\n"
      "endinterface\n"));
}

// --- function_data_type_or_implicit: signed implicit ---

TEST(FunctionDeclParsing, FunctionImplicitReturnTypeSigned) {
  auto r = Parse(
      "module m;\n"
      "  function signed [7:0] f(); return -1; endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstFunctionDecl(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->return_type.is_signed);
  EXPECT_NE(item->return_type.packed_dim_left, nullptr);
}

// --- function_data_type_or_implicit: named type ---

TEST(FunctionDeclParsing, FunctionNamedReturnType) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  typedef struct packed { logic [7:0] data; } my_t;\n"
      "  function my_t f(); return '0; endfunction\n"
      "endmodule\n"));
}

// --- function_prototype with dynamic_override_specifiers ---

TEST(FunctionDeclParsing, FunctionPrototypeWithOverride) {
  EXPECT_TRUE(ParseOk(
      "class C;\n"
      "  pure virtual function :initial void f();\n"
      "endclass\n"));
}

// --- function_prototype with args ---

TEST(FunctionDeclParsing, FunctionPrototypeWithArgs) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  import \"DPI-C\" function int add(int a, int b);\n"
      "endmodule\n"));
}

// --- dpi_task_import_property: context on task ---

TEST(FunctionDeclParsing, DpiImportTaskContext) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" context task ctx_task();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kDpiImport);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->dpi_is_task);
  EXPECT_TRUE(item->dpi_is_context);
}

// --- dpi_import_export: DPI import with C identifier on task ---

TEST(FunctionDeclParsing, DpiImportTaskWithCIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  import \"DPI-C\" c_task_name = task sv_task();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kDpiImport);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->dpi_is_task);
  EXPECT_EQ(item->dpi_c_name, "c_task_name");
}

// --- dpi_import_export: DPI export task with C identifier ---

TEST(FunctionDeclParsing, DpiExportTaskWithCIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(); endtask\n"
      "  export \"DPI-C\" c_alias = task my_task;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kDpiExport);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->dpi_is_task);
  EXPECT_EQ(item->dpi_c_name, "c_alias");
}

// --- dynamic_override_specifiers: combined extends:final ---

TEST(FunctionDeclParsing, FunctionDynOverrideExtendsFinal) {
  EXPECT_TRUE(ParseOk(
      "class c;\n"
      "  virtual function :extends :final void f(); endfunction\n"
      "endclass\n"));
}

}  // namespace
