#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §3.9: Packages provide a shared declaration space.

TEST(ParserClause03, Cl3_9_PackageEnclosedByKeywords) {
  auto r = Parse("package pkg; endpackage");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

TEST(ParserClause03, Cl3_9_PackageWithTypedef) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->packages[0]->items.empty());
}

TEST(ParserClause03, Cl3_9_PackageWithFunction) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  function int add(int a, int b); return a + b; endfunction\n"
              "endpackage\n"));
}

// §3.9: Package declarations can be imported into other building blocks.

TEST(ParserClause03, Cl3_9_ImportIntoModule) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int myint;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kImportDecl));
}

TEST(ParserClause03, Cl3_9_ImportIntoInterface) {
  EXPECT_TRUE(
      ParseOk("package pkg; typedef int myint; endpackage\n"
              "interface ifc;\n"
              "  import pkg::*;\n"
              "endinterface\n"));
}

TEST(ParserClause03, Cl3_9_ImportIntoProgram) {
  EXPECT_TRUE(
      ParseOk("package pkg; typedef int myint; endpackage\n"
              "program p;\n"
              "  import pkg::*;\n"
              "endprogram\n"));
}

TEST(ParserClause03, Cl3_9_ImportIntoPackage) {
  EXPECT_TRUE(
      ParseOk("package a; typedef int myint; endpackage\n"
              "package b;\n"
              "  import a::*;\n"
              "endpackage\n"));
}

TEST(ParserClause03, Cl3_9_NamedImport) {
  auto r = Parse(
      "package pkg; typedef int myint; endpackage\n"
      "module m;\n"
      "  import pkg::myint;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §3.9: LRM ComplexPkg example.

TEST(ParserClause03, Cl3_9_ComplexPkgExample) {
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

// §3.9: Module/interface/program/checker declarations are local.

TEST(ParserClause03, Cl3_9_LocalScopesDoNotConflict) {
  EXPECT_TRUE(
      ParseOk("module a; logic x; endmodule\n"
              "module b; logic x; endmodule\n"));
}

}  // namespace
