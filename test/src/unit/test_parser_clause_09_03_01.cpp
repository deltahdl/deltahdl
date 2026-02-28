// §9.3.1: Sequential blocks

#include "fixture_parser.h"

using namespace delta;

namespace {

// attribute_instance prefix on block items
TEST(ParserA28, AttrOnDataDeclInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* synthesis *) int x;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserA28, AttrOnLocalparamInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* synthesis *) localparam int X = 5;\n"
              "  end\n"
              "endmodule\n"));
}

// §A.2.8 block_item_declaration alternative 1: data_declaration
// data_declaration ::= [ const ] [ var ] [ lifetime ] data_type_or_implicit
//                      list_of_variable_decl_assignments ;
TEST(ParserA28, DataDeclBasicInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_name, "x");
}

}  // namespace
