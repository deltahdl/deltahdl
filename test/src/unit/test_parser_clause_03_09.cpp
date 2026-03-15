// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, PackageWithTypedef) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->packages[0]->items.empty());
}

TEST(DesignBuildingBlockParsing, PackageWithFunction) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  function int add(int a, int b); return a + b; endfunction\n"
              "endpackage\n"));
}

TEST(DesignBuildingBlockParsing, ImportIntoModule) {
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

TEST(DesignBuildingBlockParsing, ImportIntoInterface) {
  EXPECT_TRUE(
      ParseOk("package pkg; typedef int myint; endpackage\n"
              "interface ifc;\n"
              "  import pkg::*;\n"
              "endinterface\n"));
}

TEST(DesignBuildingBlockParsing, ImportIntoProgram) {
  EXPECT_TRUE(
      ParseOk("package pkg; typedef int myint; endpackage\n"
              "program p;\n"
              "  import pkg::*;\n"
              "endprogram\n"));
}

TEST(DesignBuildingBlockParsing, ImportIntoPackage) {
  EXPECT_TRUE(
      ParseOk("package a; typedef int myint; endpackage\n"
              "package b;\n"
              "  import a::*;\n"
              "endpackage\n"));
}

TEST(DesignBuildingBlockParsing, NamedImport) {
  auto r = Parse(
      "package pkg; typedef int myint; endpackage\n"
      "module m;\n"
      "  import pkg::myint;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DesignBuildingBlockParsing, ComplexPkgExample) {
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

TEST(DesignBuildingBlockParsing, LocalScopesDoNotConflict) {
  EXPECT_TRUE(
      ParseOk("module a; logic x; endmodule\n"
              "module b; logic x; endmodule\n"));
}

}  // namespace
