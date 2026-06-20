#include "fixture_parser.h"

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

static bool ParseOk5(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

TEST(DataObjectParsing, ModuleBody_NullItem) {
  EXPECT_TRUE(ParseOk5("module m; ; endmodule"));
}

TEST(PackageDeclaration, PackageEndLabel) {
  auto r = Parse("package bar; endpackage : bar\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "bar");
}

TEST(PackageDeclaration, MissingEndpackageIsError) {
  EXPECT_FALSE(ParseOk("package p;"));
}

TEST(PackageDeclaration, PackageNotAllowedInsideModule) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  package inner;\n"
              "  endpackage\n"
              "endmodule\n"));
}

TEST(PackageDeclaration, PackageNotAllowedInsideInterface) {
  EXPECT_FALSE(
      ParseOk("interface ifc;\n"
              "  package inner;\n"
              "  endpackage\n"
              "endinterface\n"));
}

TEST(PackageDeclaration, PackageNotAllowedInsideProgram) {
  EXPECT_FALSE(
      ParseOk("program prg;\n"
              "  package inner;\n"
              "  endpackage\n"
              "endprogram\n"));
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
  EXPECT_FALSE(ParseOk("package ; endpackage\n"));
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

}  // namespace
