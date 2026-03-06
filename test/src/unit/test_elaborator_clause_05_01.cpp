#include "fixture_elaborator.h"

namespace {

// §5.1: Clause 5 covers lexical tokens, literals, built-in method calls,
// and attributes. Verify that the elaborator accepts modules using all
// four areas described in the overview.

TEST(ElabClause05, Cl5_1_ModuleWithIntegerLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] x = 8'hFF;\n"
             "endmodule\n"));
}

TEST(ElabClause05, Cl5_1_ModuleWithRealLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  real r = 3.14;\n"
             "endmodule\n"));
}

TEST(ElabClause05, Cl5_1_ModuleWithStringLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial $display(\"hello\");\n"
             "endmodule\n"));
}

TEST(ElabClause05, Cl5_1_ModuleWithAttributeElaborates) {
  EXPECT_TRUE(
      ElabOk("(* synthesis *) module t;\n"
             "  logic a;\n"
             "endmodule\n"));
}

TEST(ElabClause05, Cl5_1_ModuleWithTimeLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial #10ns;\n"
             "endmodule\n"));
}

TEST(ElabClause05, Cl5_1_ModuleWithUnbasedUnsizedLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [15:0] x;\n"
             "  assign x = '1;\n"
             "endmodule\n"));
}

TEST(ElabClause05, Cl5_1_ModuleWithArrayLiteralElaborates) {
  // §5.11: array literals use '{ } syntax
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int arr [0:1];\n"
             "  initial arr = '{0, 1};\n"
             "endmodule\n"));
}

TEST(ElabClause05, Cl5_1_ModuleWithStructureLiteralElaborates) {
  // §5.10: structure literals use '{ } syntax
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct { int a; int b; } ab_t;\n"
             "  ab_t s;\n"
             "  initial s = '{0, 1};\n"
             "endmodule\n"));
}

TEST(ElabClause05, Cl5_1_ModuleWithBuiltinMethodElaborates) {
  // §5.13: built-in methods use dot notation
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int q[$];\n"
             "  int sz;\n"
             "  initial sz = q.size();\n"
             "endmodule\n"));
}

TEST(ElabClause05, Cl5_1_ModuleWithEscapedIdentifierElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic \\bus+a ;\n"
             "  assign \\bus+a = 1'b0;\n"
             "endmodule\n"));
}

TEST(ElabClause05, Cl5_1_AllFourAreasElaborate) {
  EXPECT_TRUE(
      ElabOk("(* optimize *) module t;\n"
             "  logic [7:0] data = 8'hAB;\n"
             "  real pi = 3.14;\n"
             "  initial $display(\"all areas: %d\", data);\n"
             "endmodule\n"));
}

TEST(ElabClause05, Cl5_1_CommentsDoNotAffectElaboration) {
  EXPECT_TRUE(
      ElabOk("module /* block */ t; // line comment\n"
             "  logic /* type */ a; // declaration\n"
             "  assign /* continuous */ a = /* rhs */ 1'b1;\n"
             "endmodule /* end */\n"));
}

}  // namespace
