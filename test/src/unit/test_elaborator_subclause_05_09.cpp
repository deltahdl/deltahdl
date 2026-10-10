#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LexicalConventionElaboration, ModuleWithStringLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial $display(\"hello\");\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, TripleQuotedStringElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial $display(\"\"\"hello\"\"\");\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, StringAssignmentToByteElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  byte c;\n"
             "  initial c = \"A\";\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, StringAssignmentToPackedArrayElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  bit [8*5:1] s;\n"
             "  initial s = \"Hello\";\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, EmptyStringElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  initial $display(\"\");\n"
             "endmodule\n"));
}

// §5.9: a string literal used as an operand is an unsigned integral constant of
// one 8-bit value per character or escape, so "a\0" is 16 bits, 'h6100. Only a
// string variable drops \0 (§6.16). The parameter fold dropped it, giving P
// 'h0061 and Q 8 bits.
TEST(LexicalConventionElaboration,
     StringLiteralFoldedAsAnIntegerKeepsZeroBytes) {
  SimFixture f;
  auto* p = RunAndFindVar(
      "module t;\n"
      "  localparam [15:0] P = \"a\\0\";\n"
      "  parameter Q = \"a\\0\";\n"
      "  localparam int W = $bits(Q);\n"
      "  logic [15:0] p;\n"
      "  int w;\n"
      "  initial begin p = P; w = W; end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->value.ToUint64(), 0x6100u);
  EXPECT_EQ(f.ctx.FindVariable("w")->value.ToUint64(), 16u);
}

}  // namespace
