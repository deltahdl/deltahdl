#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(PackageItemsParsing, NetDeclaration) {
  auto r = Parse(
      "package p;\n"
      "  wire w;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, DataDeclaration) {
  auto r = Parse(
      "package p;\n"
      "  int x = 42;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, TaskDeclaration) {
  auto r = Parse(
      "package p;\n"
      "  task do_work();\n"
      "  endtask\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, FunctionDeclaration) {
  auto r = Parse(
      "package p;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kFunctionDecl));
}

TEST(PackageItemsParsing, CheckerInPackage) {
  auto r = Parse(
      "package p;\n"
      "  checker my_chk;\n"
      "  endchecker\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, DpiImport) {
  auto r = Parse(
      "package p;\n"
      "  import \"DPI-C\" function int c_func(int x);\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kDpiImport));
}

TEST(PackageItemsParsing, ClassInPackage) {
  auto r = Parse(
      "package p;\n"
      "  class Pkt;\n"
      "    int data;\n"
      "  endclass\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, InterfaceClassInPackage) {
  auto r = Parse(
      "package p;\n"
      "  interface class IFace;\n"
      "    pure virtual function void work();\n"
      "  endclass\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, LocalparamInPackage) {
  auto r = Parse(
      "package p;\n"
      "  localparam int MAX = 255;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, ParameterInPackage) {
  auto r = Parse(
      "package p;\n"
      "  parameter int WIDTH = 8;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, CovergroupInPackage) {
  auto r = Parse(
      "package p;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, PropertyInPackage) {
  auto r = Parse(
      "package p;\n"
      "  property prop_req;\n"
      "    @(posedge clk) req |-> ##[1:3] ack;\n"
      "  endproperty\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, NullItem) {
  auto r = Parse(
      "package p;\n"
      "  ;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, AnonymousProgram) {
  auto r = Parse(
      "package p;\n"
      "  program;\n"
      "    task run();\n"
      "    endtask\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, PackageExport) {
  auto r = Parse(
      "package p;\n"
      "  import other_pkg::*;\n"
      "  export other_pkg::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, PackageTimeunits) {
  auto r = Parse(
      "package p;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, PackageTypedef) {
  auto r = Parse(
      "package p;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, PackageImport) {
  auto r = Parse(
      "package p;\n"
      "  import other_pkg::item;\n"
      "  import another_pkg::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, ClassConstructorInPackage) {
  auto r = Parse(
      "package p;\n"
      "  class C;\n"
      "    function new(int val);\n"
      "    endfunction\n"
      "  endclass\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, MixedPackageItems) {
  auto r = Parse(
      "package p;\n"
      "  parameter int W = 8;\n"
      "  typedef logic [W-1:0] data_t;\n"
      "  function data_t zero();\n"
      "    return '0;\n"
      "  endfunction\n"
      "  class Pkt;\n"
      "    data_t payload;\n"
      "  endclass\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_GE(r.cu->packages[0]->items.size(), 3u);
}

// --- Moved from test_parser_clause_26_02.cpp ---

TEST(PackageItemsParsing, PackageWithParameter) {
  auto r = Parse(
      "package cfg_pkg;\n"
      "  parameter int WIDTH = 8;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  ASSERT_FALSE(r.cu->packages[0]->items.empty());
}

TEST(PackageItemsParsing, PackageWithFunction) {
  auto r = Parse(
      "package util_pkg;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kFunctionDecl));
}

TEST(PackageItemsParsing, PackageWithStructTypedef) {
  auto r = Parse(
      "package types_pkg;\n"
      "  typedef struct {\n"
      "    shortreal i, r;\n"
      "  } Complex;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kTypedef));
}

TEST(PackageItemsParsing, PackageWithClassDecl) {
  auto r = Parse(
      "package cls_pkg;\n"
      "  class transaction;\n"
      "    int addr;\n"
      "  endclass\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kClassDecl));
}

TEST(PackageItemsParsing, PackageWithParamVerifiesAst) {
  auto r = Parse(
      "package my_pkg;\n"
      "  parameter int WIDTH = 8;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1);
  ASSERT_EQ(r.cu->packages[0]->items.size(), 1);
  EXPECT_EQ(r.cu->packages[0]->items[0]->kind, ModuleItemKind::kParamDecl);
}

TEST(PackageItemsParsing, PackageOrGenerateItemDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  wire w;\n"
      "  int x;\n"
      "  function void f(); endfunction\n"
      "  task t(); endtask\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_GE(r.cu->packages[0]->items.size(), 4u);
}

TEST(PackageItemsParsing, PackageItemCheckerDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  checker chk; endchecker\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, PackageItemClassDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  class C;\n"
      "    int x;\n"
      "  endclass\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, PackageItemInterfaceClassDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  interface class IC;\n"
      "    pure virtual function void f();\n"
      "  endclass\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, PackageItemClassConstructorDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  function MyClass::new(); endfunction\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, PackageItemLocalparamDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  localparam int A = 1;\n"
      "  parameter int B = 2;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_GE(r.cu->packages[0]->items.size(), 2u);
}

TEST(PackageItemsParsing, PackageItemCovergroupDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  covergroup cg; endgroup\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, PackageItemAssertionDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  property p; 1; endproperty\n"
      "  sequence s; 1; endsequence\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, PackageItemEmptyStmt) {
  auto r = Parse(
      "package pkg;\n"
      "  ;\n"
      "  ;;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, PackageWithInternalDeclarations) {
  auto r = Parse(
      "package my_pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  parameter int WIDTH = 8;\n"
      "  function automatic int double_it(int x);\n"
      "    return x * 2;\n"
      "  endfunction\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  auto* pkg = r.cu->packages[0];
  EXPECT_EQ(pkg->name, "my_pkg");
  EXPECT_GE(pkg->items.size(), 3u);
}

TEST(PackageItemsParsing, PackageContainsDeclarations) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int myint;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->packages[0]->items.empty());
}

TEST(PackageItemsParsing, SimpleTypedefInPackage) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->packages[0]->items.empty());
}

TEST(PackageItemsParsing, SimpleFunctionInPackage) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  function int add(int a, int b); return a + b; endfunction\n"
              "endpackage\n"));
}

TEST(PackageItemsParsing, ComplexPkgExample) {
  auto r = Parse(
      "package ComplexPkg;\n"
      "  typedef struct {\n"
      "    shortreal i, r;\n"
      "  } Complex;\n"
      "  function Complex add(Complex a, b);\n"
      "    add.r = a.r + b.r;\n"
      "    add.i = a.i + b.i;\n"
      "  endfunction\n"
      "  function Complex mul(Complex a, b);\n"
      "    mul.r = (a.r * b.r) - (a.i * b.i);\n"
      "    mul.i = (a.r * b.i) + (a.i * b.r);\n"
      "  endfunction\n"
      "endpackage : ComplexPkg\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "ComplexPkg");
}

// --- Moved from test_parser_clause_26_06.cpp ---

TEST(PackageItemsParsing, PackageExportMultipleItems) {
  auto r = Parse(
      "package pkg;\n"
      "  export p1::a, p2::b;\n"
      "endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int export_count = 0;
  for (auto* item : r.cu->packages[0]->items) {
    if (item->kind == ModuleItemKind::kExportDecl) export_count++;
  }
  EXPECT_GE(export_count, 2);
}

TEST(PackageItemsParsing, PackageExportWildcard) {
  auto r = Parse(
      "package p;\n"
      "  export *::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kExportDecl));
}

TEST(PackageItemsParsing, PackageExportSpecific) {
  auto r = Parse(
      "package p;\n"
      "  export other_pkg::some_func;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, ExportDeclVerifiesAst) {
  auto r = Parse(
      "package p;\n"
      "  export pkg::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  auto* pkg = r.cu->packages[0];
  ASSERT_EQ(pkg->items.size(), 1);
  EXPECT_EQ(pkg->items[0]->kind, ModuleItemKind::kExportDecl);
  EXPECT_EQ(pkg->items[0]->import_item.package_name, "pkg");
  EXPECT_TRUE(pkg->items[0]->import_item.is_wildcard);
}

TEST(PackageItemsParsing, ExportWildcardAllVerifiesAst) {
  auto r = Parse(
      "package p;\n"
      "  export *::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  auto* pkg = r.cu->packages[0];
  ASSERT_EQ(pkg->items.size(), 1);
  EXPECT_EQ(pkg->items[0]->kind, ModuleItemKind::kExportDecl);
  EXPECT_EQ(pkg->items[0]->import_item.package_name, "*");
  EXPECT_TRUE(pkg->items[0]->import_item.is_wildcard);
}

TEST(PackageItemsParsing, PackageExportNamed) {
  auto r = Parse(
      "package pkg;\n"
      "  export other_pkg::my_func;\n"
      "  export another::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_GE(r.cu->packages[0]->items.size(), 2u);
}

TEST(PackageItemsParsing, PackageExportSingleItem) {
  auto r = Parse(
      "package pkg;\n"
      "  export other_pkg::some_func;\n"
      "endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->packages[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kExportDecl);
  EXPECT_EQ(item->import_item.package_name, "other_pkg");
  EXPECT_EQ(item->import_item.item_name, "some_func");
}

// --- Moved from test_parser_clause_24_03.cpp ---

TEST(PackageItemsParsing, AnonymousProgramClasses) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    class C; endclass\n"
      "    interface class IC;\n"
      "      pure virtual function void f();\n"
      "    endclass\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, AnonymousProgramMisc) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    covergroup cg; endgroup\n"
      "    function MyClass::new(); endfunction\n"
      "    ;\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

// --- Moved from test_parser_clause_24_06.cpp ---

TEST(PackageItemsParsing, AnonymousProgramFunctionAndTask) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    function void f(); endfunction\n"
      "    task t(); endtask\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, AnonymousProgramTopLevel) {
  auto r = Parse(
      "program;\n"
      "  function void f(); endfunction\n"
      "  class C; endclass\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- Moved from test_parser_clause_35_05_04.cpp ---

TEST(PackageItemsParsing, PackageItemDpiImportExport) {
  auto r = Parse(
      "package pkg;\n"
      "  import \"DPI-C\" function void c_func();\n"
      "  export \"DPI-C\" function sv_func;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_GE(r.cu->packages[0]->items.size(), 2u);
}

// --- New coverage tests ---

TEST(PackageItemsParsing, ExternConstraintDeclInPackage) {
  auto r = Parse(
      "package pkg;\n"
      "  class C;\n"
      "    constraint c1;\n"
      "  endclass\n"
      "  constraint C::c1 { }\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, AnonymousProgramEmpty) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, AnonymousProgramInterfaceClass) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    interface class IC;\n"
      "      pure virtual function void g();\n"
      "    endclass\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, AnonymousProgramCovergroup) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    covergroup cg;\n"
      "      coverpoint x;\n"
      "    endgroup\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, AnonymousProgramNullItems) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    ;\n"
      "    ;;\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, AnonymousProgramClassConstructor) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    function MyClass::new();\n"
      "    endfunction\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, MultipleAnonymousPrograms) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    task t1(); endtask\n"
      "  endprogram\n"
      "  program;\n"
      "    task t2(); endtask\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, AllPackageItemAlternatives) {
  auto r = Parse(
      "package pkg;\n"
      "  wire w;\n"
      "  int x;\n"
      "  task t(); endtask\n"
      "  function int f(); return 0; endfunction\n"
      "  checker chk; endchecker\n"
      "  import \"DPI-C\" function void c_fn();\n"
      "  class C; endclass\n"
      "  interface class IC;\n"
      "    pure virtual function void g();\n"
      "  endclass\n"
      "  localparam int A = 1;\n"
      "  parameter int B = 2;\n"
      "  covergroup cg; endgroup\n"
      "  property p; 1; endproperty\n"
      "  ;\n"
      "  timeunit 1ns;\n"
      "  export other_pkg::*;\n"
      "  program;\n"
      "    task inner_t(); endtask\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_GE(r.cu->packages[0]->items.size(), 10u);
}

// --- Error tests ---

TEST(PackageItemsParsing, ErrorAnonymousProgramWithPorts) {
  EXPECT_FALSE(ParseOk(
      "package pkg;\n"
      "  program(input clk);\n"
      "  endprogram\n"
      "endpackage\n"));
}

TEST(PackageItemsParsing, ErrorAnonymousProgramMissingEndprogram) {
  EXPECT_FALSE(ParseOk(
      "package pkg;\n"
      "  program;\n"
      "    task t(); endtask\n"
      "endpackage\n"));
}

TEST(PackageItemsParsing, ErrorAnonymousProgramWithName) {
  EXPECT_FALSE(ParseOk(
      "package pkg;\n"
      "  program named_prog;\n"
      "  endprogram\n"
      "endpackage\n"));
}

TEST(PackageItemsParsing, ErrorAnonymousProgramWithNetDecl) {
  EXPECT_FALSE(ParseOk(
      "package pkg;\n"
      "  program;\n"
      "    wire w;\n"
      "  endprogram\n"
      "endpackage\n"));
}

TEST(PackageItemsParsing, ErrorAnonymousProgramWithDataDecl) {
  EXPECT_FALSE(ParseOk(
      "package pkg;\n"
      "  program;\n"
      "    int x;\n"
      "  endprogram\n"
      "endpackage\n"));
}

TEST(PackageItemsParsing, SequenceInPackage) {
  auto r = Parse(
      "package pkg;\n"
      "  sequence s_req;\n"
      "    req ##[1:3] ack;\n"
      "  endsequence\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageItemsParsing, DpiExportStandalone) {
  auto r = Parse(
      "package pkg;\n"
      "  export \"DPI-C\" function sv_func;\n"
      "  export \"DPI-C\" task sv_task;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_GE(r.cu->packages[0]->items.size(), 2u);
}

TEST(PackageItemsParsing, AnonymousProgramAllItemTypes) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    task t(); endtask\n"
      "    function void f(); endfunction\n"
      "    class C; endclass\n"
      "    interface class IC;\n"
      "      pure virtual function void g();\n"
      "    endclass\n"
      "    function MyClass::new(); endfunction\n"
      "    covergroup cg; endgroup\n"
      "    ;\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageItemsParsing, PackageOnlyExports) {
  auto r = Parse(
      "package pkg;\n"
      "  export other_pkg::item1;\n"
      "  export *::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->items.size(), 2u);
}

TEST(PackageItemsParsing, PackageOnlyNullItems) {
  auto r = Parse(
      "package pkg;\n"
      "  ;\n"
      "  ;\n"
      "  ;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
