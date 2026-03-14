#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(LexicalConventionElaboration, PositionalStructLiteral) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  ab_t c;\n"
             "  initial c = '{8'hAA, 8'hBB};\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, NamedMemberStructLiteral) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  ab_t c;\n"
             "  initial c = '{a: 8'h11, b: 8'h22};\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, DefaultStructLiteral) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  ab_t c;\n"
             "  initial c = '{default: 8'hFF};\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, TypePrefixedPattern) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] x; logic [7:0] y; } pt_t;\n"
             "  pt_t c;\n"
             "  initial c = pt_t'{x: 8'h05, y: 8'h0A};\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, StructLiteralVarInit) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  ab_t c = '{8'h55, 8'hAA};\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, InvalidMemberName) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s = "
      "'{nonexistent: 8'hFF};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(LexicalConventionElaboration, DuplicateMemberKey) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s = "
      "'{a: 8'h01, a: 8'h02};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
