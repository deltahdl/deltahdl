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
