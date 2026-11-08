#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(PackageDeclarationParsing, PackageLifetimeWithItems) {
  auto r = Parse(
      "package automatic pkg;\n"
      "  parameter int W = 8;\n"
      "  typedef logic [W-1:0] word_t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  EXPECT_EQ(r.cu->packages[0]->items.size(), 2u);
}

TEST(PackageParsing, MultiplePackages) {
  auto r = Parse(
      "package a;\n"
      "endpackage\n"
      "package b;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 2u);
  EXPECT_EQ(r.cu->packages[0]->name, "a");
  EXPECT_EQ(r.cu->packages[1]->name, "b");
}

TEST(PackageDeclarationParsing, PackageAutomaticLifetime) {
  auto r = Parse("package automatic pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

TEST(PackageDeclarationParsing, PackageStaticLifetime) {
  auto r = Parse("package static pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

TEST(PackageDeclarationParsing, PackageDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  parameter int W = 8;\n"
      "  typedef logic [W-1:0] word_t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

TEST(PackageParsing, EmptyPackage) {
  auto r = Parse(
      "package pkg;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

TEST(DataObjectParsing, ModuleBody_NullItem) {
  EXPECT_TRUE(ParseOk("module m; ; endmodule"));
}

TEST(PackageDeclaration, PackageEndLabel) {
  auto r = Parse("package bar; endpackage : bar\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "bar");
}

TEST(PackageDeclaration, MissingEndpackageIsError) {
  auto r = Parse("package p;");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endpackage', got EOF", 1, "26.2"));
}

TEST(PackageDeclaration, RepeatedTimeunitMustMatchThePreviousOne) {
  auto r = Parse(
      "package pkg;\n"
      "  timeunit 1ns;\n"
      "  timeunit 1ps;\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "timeunit does not match prior declaration", 3, "3.14.2.2"));
}

TEST(PackageDeclaration, RepeatedTimeprecisionMustMatchThePreviousOne) {
  auto r = Parse(
      "package pkg;\n"
      "  timeprecision 1ps;\n"
      "  timeprecision 1fs;\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "timeprecision does not match prior declaration", 3,
                            "3.14.2.2"));
}

TEST(PackageDeclaration, ARepeatedTimeunitThatMatchesIsAccepted) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  timeunit 1ns;\n"
              "  timeunit 1ns;\n"
              "endpackage\n"));
}

TEST(PackageDeclaration, PackageNotAllowedInsideModule) {
  auto r = Parse(
      "module m;\n"
      "  package inner;\n"
      "  endpackage\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "unexpected token in module body", 2, "23.2.4"));
}

TEST(PackageDeclaration, PackageNotAllowedInsideInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  package inner;\n"
      "  endpackage\n"
      "endinterface\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "unexpected token in module body", 2, "23.2.4"));
}

TEST(PackageDeclaration, PackageNotAllowedInsideProgram) {
  auto r = Parse(
      "program prg;\n"
      "  package inner;\n"
      "  endpackage\n"
      "endprogram\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "unexpected token in module body", 2, "23.2.4"));
}

TEST(PackageDeclaration, NullItemInPackageBody) {
  auto r = Parse(
      "package pkg;\n"
      "  ;\n"
      "  parameter int W = 4;\n"
      "  ;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

TEST(PackageDeclaration, LocalparamAsPackageItem) {
  auto r = Parse(
      "package pkg;\n"
      "  localparam int W = 8;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  ASSERT_FALSE(r.cu->packages[0]->items.empty());
  EXPECT_EQ(r.cu->packages[0]->items[0]->kind, ModuleItemKind::kParamDecl);
}

TEST(PackageDeclaration, MissingPackageIdentifierIsError) {
  auto r = Parse("package ; endpackage\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 1, "26.2"));
}

TEST(PackageDeclaration, AnonymousProgramAsPackageItem) {
  auto r = Parse(
      "package pkg;\n"
      "  program;\n"
      "    function int f; return 1; endfunction\n"
      "  endprogram\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

TEST(PackageDeclaration, FunctionDeclarationAsPackageItem) {
  auto r = Parse(
      "package pkg;\n"
      "  function int f(int x); return x; endfunction\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_FALSE(r.cu->packages[0]->items.empty());
  EXPECT_EQ(r.cu->packages[0]->items[0]->kind, ModuleItemKind::kFunctionDecl);
}

TEST(PackageDeclaration, TaskDeclarationAsPackageItem) {
  auto r = Parse(
      "package pkg;\n"
      "  task t; endtask\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_FALSE(r.cu->packages[0]->items.empty());
  EXPECT_EQ(r.cu->packages[0]->items[0]->kind, ModuleItemKind::kTaskDecl);
}

TEST(PackageDeclaration, ClassDeclarationAsPackageItem) {
  auto r = Parse(
      "package pkg;\n"
      "  class C; int x; endclass\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_FALSE(r.cu->packages[0]->items.empty());
  EXPECT_EQ(r.cu->packages[0]->items[0]->kind, ModuleItemKind::kClassDecl);
}

TEST(PackageDeclaration, NetDeclarationAsPackageItem) {
  auto r = Parse(
      "package pkg;\n"
      "  wire w;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_FALSE(r.cu->packages[0]->items.empty());
  EXPECT_EQ(r.cu->packages[0]->items[0]->kind, ModuleItemKind::kNetDecl);
}

TEST(PackageDeclaration, VariableDeclarationAsPackageItem) {
  auto r = Parse(
      "package pkg;\n"
      "  int v;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_FALSE(r.cu->packages[0]->items.empty());
  EXPECT_EQ(r.cu->packages[0]->items[0]->kind, ModuleItemKind::kVarDecl);
}

TEST(PackageDeclaration, PackageExportDeclarationAsPackageItem) {
  auto r = Parse(
      "package src;\n"
      "  typedef int t;\n"
      "endpackage\n"
      "package pkg;\n"
      "  import src::*;\n"
      "  export src::*;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 2u);
  bool found_export = false;
  for (auto* it : r.cu->packages[1]->items) {
    if (it->kind == ModuleItemKind::kExportDecl) {
      found_export = true;
      break;
    }
  }
  EXPECT_TRUE(found_export);
}

TEST(PackageDeclaration, AttributeInstanceBeforePackageAccepted) {
  auto r = Parse(
      "(* keep *) package pkg;\n"
      "  parameter int W = 4;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  EXPECT_EQ(r.cu->packages[0]->items.size(), 1u);
}

TEST(PackageDeclaration, AttributeInstanceBeforePackageItemAccepted) {
  auto r = Parse(
      "package pkg;\n"
      "  (* my_attr = 1 *) int v;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  ASSERT_FALSE(r.cu->packages[0]->items.empty());
  EXPECT_EQ(r.cu->packages[0]->items[0]->kind, ModuleItemKind::kVarDecl);
}

TEST(PackageDeclaration, ExternConstraintDeclarationAsPackageItem) {
  auto r = Parse(
      "package pkg;\n"
      "  class C;\n"
      "    rand int x;\n"
      "    constraint c;\n"
      "  endclass\n"
      "  constraint C::c { x > 0; }\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->external_constraints.size(), 1u);
}

TEST(PackageDeclaration, TimeunitsDeclarationAsPackageItem) {
  auto r = Parse(
      "package pkg;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(PackageDeclaration, MalformedPackageHeaderNames26_2) {
  auto r = Parse(
      "package ;\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier", 1, "26.2"));
}

TEST(PackageDeclaration, CheckerInAPackageMayDeclareAClockingBlock) {
  auto r = Parse(
      "package p;\n"
      "  checker chk(logic a, logic clk);\n"
      "    default clocking cb @(posedge clk); endclocking\n"
      "    a1: assert property (a);\n"
      "  endchecker\n"
      "endpackage\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(PackageDeclaration, ClockingBlockOfThePackageItselfStaysReported) {
  auto r = Parse(
      "package p;\n"
      "  checker chk(logic a); endchecker\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "endpackage\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a package body cannot hold a clocking block", 3, "14.7"));
}

}  // namespace
