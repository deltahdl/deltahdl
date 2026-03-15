#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SourceText, DescriptionPackage) {
  auto r = Parse("package pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

TEST(SourceText, PackageLifetimeWithItems) {
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

TEST(PackageParsing, PackageWithParameter) {
  auto r = Parse(
      "package cfg_pkg;\n"
      "  parameter int WIDTH = 8;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  ASSERT_FALSE(r.cu->packages[0]->items.empty());
}

TEST(PackageParsing, PackageWithFunction) {
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

TEST(PackageParsing, PackageWithStructTypedef) {
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

TEST(PackageParsing, PackageWithClassDecl) {
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

TEST(Parser, PackageWithParam) {
  auto r = Parse(
      "package my_pkg;\n"
      "  parameter int WIDTH = 8;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1);
  ASSERT_EQ(r.cu->packages[0]->items.size(), 1);
  EXPECT_EQ(r.cu->packages[0]->items[0]->kind, ModuleItemKind::kParamDecl);
}

TEST(SourceText, PackageOrGenerateItemDecl) {
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

TEST(SourceText, PackageItemCheckerDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  checker chk; endchecker\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}
TEST(ModuleAndHierarchyParsing, EndLabelPackage) {
  auto r = Parse("package mypkg; endpackage : mypkg\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1);
  EXPECT_EQ(r.cu->packages[0]->name, "mypkg");
}

TEST(SourceText, PackageItemClassDecl) {
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

TEST(SourceText, PackageItemInterfaceClassDecl) {
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

TEST(SourceText, PackageItemClassConstructorDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  function MyClass::new(); endfunction\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(SourceText, PackageItemLocalparamDecl) {
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

TEST(SourceText, PackageItemCovergroupDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  covergroup cg; endgroup\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(SourceText, PackageItemAssertionDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  property p; 1; endproperty\n"
      "  sequence s; 1; endsequence\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(SourceText, PackageItemEmptyStmt) {
  auto r = Parse(
      "package pkg;\n"
      "  ;\n"
      "  ;;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

TEST(DesignBuildingBlockParsing, PackageWithInternalDeclarations) {
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

TEST(SourceText, PackageAutomaticLifetime) {
  auto r = Parse("package automatic pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

TEST(SourceText, PackageStaticLifetime) {
  auto r = Parse("package static pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

TEST(SourceText, PackageEndLabel) {
  auto r = Parse("package pkg; endpackage : pkg\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(FormalSyntaxParsing, PackageDecl) {
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

TEST(PackageParsing, PackageWithEndLabel) {
  auto r = Parse(
      "package my_pkg;\n"
      "endpackage : my_pkg\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "my_pkg");
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

TEST(PackageDeclarations, PackageKeywordIntroducesPackage) {
  auto r = Parse("package pkg; endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

TEST(PackageDeclarations, PackageContainsDeclarations) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int myint;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->packages[0]->items.empty());
}

TEST(PackageDeclaration, WithTypedef) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->packages[0]->items.empty());
}

TEST(PackageDeclaration, WithFunction) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  function int add(int a, int b); return a + b; endfunction\n"
              "endpackage\n"));
}

}  // namespace
