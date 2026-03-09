#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA26, FunctionDeclBasic) {
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

TEST(ParserA26, FunctionDeclLifetimeAutomatic) {
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

TEST(ParserA26, FunctionDeclLifetimeStatic) {
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

TEST(ParserA26, FunctionDeclVoidReturn) {
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

TEST(ParserA26, FunctionOldStylePorts) {
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

TEST(ParserA26, FunctionEndLabel) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function int f(); return 0; endfunction : f\n"
              "endmodule\n"));
}

TEST(ParserA26, FunctionImplicitReturnType) {
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

TEST(ParserA26, FunctionDynOverrideInitial) {
  EXPECT_TRUE(
      ParseOk("class c;\n"
              "  virtual function :initial void f(); endfunction\n"
              "endclass\n"));
}

TEST(ParserA26, FunctionDynOverrideFinal) {
  EXPECT_TRUE(
      ParseOk("class c;\n"
              "  virtual function :final void f(); endfunction\n"
              "endclass\n"));
}

TEST(ParserA26, FunctionDynOverrideExtends) {
  EXPECT_TRUE(
      ParseOk("class c;\n"
              "  virtual function :extends void f(); endfunction\n"
              "endclass\n"));
}

TEST(ParserA26, DpiImportFunction) {
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

TEST(ParserA26, DpiImportTask) {
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

TEST(ParserA26, DpiImportPure) {
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

TEST(ParserA26, DpiImportContext) {
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

TEST(ParserA26, DpiImportWithCIdentifier) {
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

TEST(ParserA26, DpiExportFunction) {
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

TEST(ParserA26, DpiExportTask) {
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

TEST(ParserA26, DpiExportWithCIdentifier) {
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

TEST(ParserA26, DpiSpecStringDPI) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  import \"DPI\" function void f();\n"
              "endmodule\n"));
}

TEST(ParserA26, FunctionPrototypeNoArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  import \"DPI-C\" function void no_args;\n"
              "endmodule\n"));
}

TEST(ParserA26, FunctionPrototypeEmptyParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  import \"DPI-C\" function void empty_args();\n"
              "endmodule\n"));
}

TEST(ParserA26, FunctionBodyWithBlockItem) {
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

}  // namespace
