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

TEST(KeywordElaboration, AllUppercaseKeywordAsIdentifierElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] MODULE;\n"
             "  assign MODULE = 8'd0;\n"
             "endmodule\n"));
}

TEST(KeywordElaboration, MultipleKeywordConstructsElaborate) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] a, b;\n"
             "  assign a = 8'd0;\n"
             "  initial begin\n"
             "    for (int i = 0; i < 2; i++) b = b + 8'd1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(KeywordElaboration, EscapedKeywordCoexistsWithKeyword) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] \\begin ;\n"
             "  initial begin\n"
             "    \\begin = 8'd42;\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
