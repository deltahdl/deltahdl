#include "fixture_elaborator.h"

namespace {

TEST(EscapedIdentifierElaboration, EscapedIdentifierElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic \\bus+a ;\n"
             "  assign \\bus+a = 1'b0;\n"
             "endmodule\n"));
}

TEST(EscapedIdentifierElaboration, EscapedKeywordAsIdentifierElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic \\module ;\n"
             "  assign \\module = 1'b0;\n"
             "endmodule\n"));
}

TEST(EscapedIdentifierElaboration, EscapedIdentifierSpecialCharsElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic \\***error-condition*** ;\n"
             "  assign \\***error-condition*** = 1'b0;\n"
             "endmodule\n"));
}

TEST(EscapedIdentifierElaboration, MultipleEscapedIdentifiersElaborate) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic \\a+b , \\c-d ;\n"
             "  assign \\a+b = 1'b0;\n"
             "  assign \\c-d = 1'b1;\n"
             "endmodule\n"));
}

TEST(EscapedIdentifierElaboration, EscapedIdentifierInExpressionElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] \\x! , result;\n"
             "  assign result = \\x! + 8'd1;\n"
             "endmodule\n"));
}

TEST(EscapedIdentifierElaboration, EscapedIdentMatchesSimpleIdent) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [7:0] cpu3;\n"
             "  assign \\cpu3 = 8'd42;\n"
             "endmodule\n"));
}

TEST(EscapedIdentifierElaboration, EscapedIdentDashClockElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic \\-clock ;\n"
             "  assign \\-clock = 1'b0;\n"
             "endmodule\n"));
}

// §5.6.1: digit-leading body — illegal as simple identifier — is legal escaped.
TEST(EscapedIdentifierElaboration, EscapedIdentAllDigitsElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic \\1234 ;\n"
             "  assign \\1234 = 1'b1;\n"
             "endmodule\n"));
}

}  // namespace
