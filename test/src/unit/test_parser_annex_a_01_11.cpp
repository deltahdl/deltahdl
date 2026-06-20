#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// package_or_generate_item_declaration alternatives (one observer per alt).
// ---------------------------------------------------------------------------

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

// Out-of-block constructor: the genuine class_constructor_declaration alt
// appearing directly as a package item.
TEST(PackageItemsParsing, PackageItemClassConstructorDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  function MyClass::new(); endfunction\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

// local_parameter_declaration and parameter_declaration alternatives.
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

// assertion_item_declaration: property and sequence forms.
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

TEST(PackageItemsParsing, NullItem) {
  auto r = Parse(
      "package p;\n"
      "  ;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
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

// ---------------------------------------------------------------------------
// package_item alternatives beyond package_or_generate_item_declaration.
// ---------------------------------------------------------------------------

TEST(PackageItemsParsing, PackageTimeunits) {
  auto r = Parse(
      "package p;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// package_export_declaration is its own package_item alternative (the named
// and the *::* wildcard forms), distinct from a DPI export.
TEST(PackageItemsParsing, PackageExportDeclaration) {
  auto r = Parse(
      "package pkg;\n"
      "  export other_pkg::*;\n"
      "  export *::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kExportDecl));
}

// ---------------------------------------------------------------------------
// Integration: every alternative coexisting in one package, including the
// package_export_declaration, timeunits, and anonymous_program alternatives.
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// anonymous_program ::= program ; { anonymous_program_item } endprogram
// ---------------------------------------------------------------------------

TEST(PackageItemsParsing, AnonymousProgramEmpty) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Every anonymous_program_item alternative: task, function, class,
// interface class, class constructor, covergroup, and the null item.
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

TEST(PackageItemsParsing, ErrorAnonymousProgramWithPorts) {
  EXPECT_FALSE(
      ParseOk("package pkg;\n"
              "  program(input clk);\n"
              "  endprogram\n"
              "endpackage\n"));
}

TEST(PackageItemsParsing, ErrorAnonymousProgramMissingEndprogram) {
  EXPECT_FALSE(
      ParseOk("package pkg;\n"
              "  program;\n"
              "    task t(); endtask\n"
              "endpackage\n"));
}

TEST(PackageItemsParsing, ErrorAnonymousProgramWithName) {
  EXPECT_FALSE(
      ParseOk("package pkg;\n"
              "  program named_prog;\n"
              "  endprogram\n"
              "endpackage\n"));
}

// net_declaration is not a legal anonymous_program_item.
TEST(PackageItemsParsing, ErrorAnonymousProgramWithNetDecl) {
  EXPECT_FALSE(
      ParseOk("package pkg;\n"
              "  program;\n"
              "    wire w;\n"
              "  endprogram\n"
              "endpackage\n"));
}

// data_declaration is not a legal anonymous_program_item.
TEST(PackageItemsParsing, ErrorAnonymousProgramWithDataDecl) {
  EXPECT_FALSE(
      ParseOk("package pkg;\n"
              "  program;\n"
              "    int x;\n"
              "  endprogram\n"
              "endpackage\n"));
}

}  // namespace
