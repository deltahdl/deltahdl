#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

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

TEST(PackageItemsParsing, PackageTimeunits) {
  auto r = Parse(
      "package p;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

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

TEST(PackageItemsParsing, AllPackageItemAlternatives) {
  auto r = Parse(
      "package pkg;\n"
      "  timeunit 1ns;\n"
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

TEST(PackageItemsParsing, AnonymousProgramEmpty) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
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
  auto r = Parse(
      "package pkg;\n"
      "  program(input clk);\n"
      "  endprogram\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got '('", 2, "24.6"));
}

TEST(PackageItemsParsing, ErrorAnonymousProgramMissingEndprogram) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    task t(); endtask\n"
      "endpackage\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endprogram', got EOF", 5, "24.6"));
}

TEST(PackageItemsParsing, ErrorAnonymousProgramWithName) {
  auto r = Parse(
      "package pkg;\n"
      "  program named_prog;\n"
      "  endprogram\n"
      "endpackage\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got identifier", 2, "24.6"));
}

constexpr std::string_view kExcludedItemMessage =
    "an anonymous program may contain only task, function, class, interface "
    "class, covergroup, and class constructor declarations";
constexpr std::string_view kExcludedItemSubclause = "A.1.11";

constexpr uint32_t kExcludedItemLine = 3;

void ExpectAnonymousProgramExcludes(const std::string& item) {
  auto r = Parse("package pkg;\n  program;\n    " + item +
                 "\n  endprogram\nendpackage\n");
  EXPECT_TRUE(ReportedError(r.diags, kExcludedItemMessage, kExcludedItemLine,
                            kExcludedItemSubclause));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(r.cu->packages[0]->items.empty());
}

TEST(PackageItemsParsing, ErrorAnonymousProgramWithNetDecl) {
  ExpectAnonymousProgramExcludes("wire w;");
}

TEST(PackageItemsParsing, ErrorAnonymousProgramWithDataDecl) {
  ExpectAnonymousProgramExcludes("int x;");
}

TEST(PackageItemsParsing, ErrorAnonymousProgramWithInitialBlock) {
  ExpectAnonymousProgramExcludes("initial begin end");
}

TEST(PackageItemsParsing, ErrorAnonymousProgramWithParameterDecl) {
  ExpectAnonymousProgramExcludes("parameter int anon_p = 1;");
}

TEST(PackageItemsParsing, ErrorAnonymousProgramWithTypedef) {
  ExpectAnonymousProgramExcludes("typedef int anon_int_t;");
}

TEST(PackageItemsParsing, ErrorAnonymousProgramWithExternalConstraintBlock) {
  ExpectAnonymousProgramExcludes("constraint C::p { 1; }");
}

TEST(PackageItemsParsing, ErrorAnonymousProgramWithModuleInst) {
  ExpectAnonymousProgramExcludes("m u0();");
}

TEST(PackageItemsParsing,
     AnonymousProgramExcludedItemsBothCiteTheGrammarClause) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    wire w;\n"
      "    initial begin end\n"
      "  endprogram\n"
      "endpackage\n");
  EXPECT_TRUE(
      ReportedError(r.diags, kExcludedItemMessage, 3, kExcludedItemSubclause));
  EXPECT_TRUE(
      ReportedError(r.diags, kExcludedItemMessage, 4, kExcludedItemSubclause));
}

TEST(PackageItemsParsing, ErrorAnonymousProgramWithTimeunitDecl) {
  ExpectAnonymousProgramExcludes("timeunit 1ns;");
}

TEST(PackageItemsParsing, ErrorAnonymousProgramWithTimeprecisionDecl) {
  ExpectAnonymousProgramExcludes("timeprecision 1ps;");
}

TEST(PackageItemsParsing, ErrorAnonymousProgramWithExternFunctionPrototype) {
  ExpectAnonymousProgramExcludes("extern function void f();");
}

TEST(PackageItemsParsing, AnonymousProgramWithFunctionDeclIsAccepted) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    function void f(); endfunction\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->items.size(), 1u);
}

TEST(PackageItemsParsing, ErrorSpecparamInPackageIsRejected) {
  auto r = Parse(
      "package pkg;\n"
      "  specparam tRise = 150;\n"
      "  int x;\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "specparam declaration must appear inside a module or a specify block", 2,
      "6.20.5"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kVarDecl));
}

TEST(PackageItemsParsing, ErrorModuleItemsInPackageAreRejected) {
  auto r = Parse(
      "package pkg;\n"
      "  assign a = b;\n"
      "  for (genvar i = 0; i < 2; i++) begin end\n"
      "  if (1) begin end\n"
      "  case (1) default: begin end endcase\n"
      "  sub u0();\n"
      "  and g0(o, a, b);\n"
      "  defparam u0.p = 1;\n"
      "  alias a = b;\n"
      "  assert property (@(posedge clk) a);\n"
      "  assume property (@(posedge clk) a);\n"
      "  cover property (@(posedge clk) a);\n"
      "  cover sequence (@(posedge clk) a);\n"
      "  restrict property (@(posedge clk) a);\n"
      "  $error(\"x\");\n"
      "  default disable iff rst;\n"
      "  module m; endmodule\n"
      "  genvar j;\n"
      "  int x;\n"
      "endpackage\n");
  const auto& d = r.diags;
  EXPECT_TRUE(ReportedError(
      d, "a continuous assignment is not an item of a package", 2, "A.1.11"));
  EXPECT_TRUE(ReportedError(
      d, "a generate construct is not an item of a package", 3, "A.1.11"));
  EXPECT_TRUE(ReportedError(
      d, "a generate construct is not an item of a package", 4, "A.1.11"));
  EXPECT_TRUE(ReportedError(
      d, "a generate construct is not an item of a package", 5, "A.1.11"));
  EXPECT_TRUE(ReportedError(d, "an instantiation is not an item of a package",
                            6, "A.1.11"));
  EXPECT_TRUE(ReportedError(
      d, "a primitive instantiation is not an item of a package", 7, "A.1.11"));
  EXPECT_TRUE(ReportedError(
      d, "a defparam statement is not an item of a package", 8, "A.1.11"));
  EXPECT_TRUE(
      ReportedError(d, "a net alias is not an item of a package", 9, "A.1.11"));
  for (int line = 10; line <= 14; ++line) {
    EXPECT_TRUE(
        ReportedError(d, "an assertion statement is not an item of a package",
                      line, "A.1.11"))
        << line;
  }
  EXPECT_TRUE(
      ReportedError(d, "an elaboration system task is not an item of a package",
                    15, "A.1.11"));
  EXPECT_TRUE(ReportedError(
      d, "a default disable iff declaration is not an item of a package", 16,
      "A.1.11"));
  EXPECT_TRUE(ReportedError(
      d,
      "a module, interface or program declaration is not an item of a "
      "package",
      17, "A.1.11"));
  EXPECT_TRUE(ReportedError(
      d, "a genvar declaration is not an item of a package", 18, "A.1.11"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  ASSERT_EQ(r.cu->packages[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(r.cu->packages[0]->items[0]->name, "x");
}

TEST(PackageItemsParsing, ErrorUdpInstanceInPackageIsRejected) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "package pkg;\n"
      "  inv u1(a, b);\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a primitive instantiation is not an item of a package", 5,
      "A.1.11"));
}

TEST(PackageItemsParsing, CheckerDeclarationInPackageIsKept) {
  auto r = Parse(
      "package pkg;\n"
      "  checker chk(input logic a);\n"
      "  endchecker\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(HasItemOfKind(r.cu->packages[0]->items,
                            ModuleItemKind::kNestedModuleDecl));
}

TEST(PackageItemsParsing, ErrorBindGenerateRegionAndPortDeclInPackage) {
  auto r = Parse(
      "package pkg;\n"
      "  bind m chk c();\n"
      "  generate\n"
      "    int y;\n"
      "  endgenerate\n"
      "  input clk;\n"
      "  int x;\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a bind directive is not an item of a package", 2, "A.1.11"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a generate region is not an item of a package", 3, "A.1.11"));
  EXPECT_TRUE(ReportedError(
      r.diags, "a port declaration is not an item of a package", 6, "A.1.11"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kVarDecl));
}

TEST(PackageItemsParsing, NestedBodiesAreNotThePackageBody) {
  auto r = Parse(
      "package pkg;\n"
      "  checker chk(input logic a);\n"
      "    assign b = a;\n"
      "  endchecker\n"
      "  program;\n"
      "    assign c = d;\n"
      "  endprogram\n"
      "endpackage\n");
  EXPECT_FALSE(ReportedError(
      r.diags, "a continuous assignment is not an item of a package", 3,
      "A.1.11"));
  EXPECT_FALSE(ReportedError(
      r.diags, "a continuous assignment is not an item of a package", 6,
      "A.1.11"));
  EXPECT_TRUE(ReportedError(
      r.diags, "an anonymous program may contain only task, function, class", 6,
      "A.1.11"));
}

}  // namespace
