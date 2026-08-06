#include "fixture_elaborator.h"

namespace {

TEST(KeywordElaboration, KeywordConstructElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] result;\n"
             "  initial begin\n"
             "    if (1) result = 8'd1;\n"
             "    else result = 8'd0;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(KeywordElaboration, EscapedKeywordAsIdentifierElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] \\begin ;\n"
             "  assign \\begin = 8'd0;\n"
             "endmodule\n"));
}

TEST(KeywordElaboration, UppercaseKeywordAsIdentifierElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] Begin;\n"
             "  assign Begin = 8'd0;\n"
             "endmodule\n"));
}

}  // namespace
