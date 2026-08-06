#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(StructLiteralElaboration, ModuleWithStructureLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct { int a; int b; } ab_t;\n"
             "  ab_t s;\n"
             "  initial s = '{0, 1};\n"
             "endmodule\n"));
}

TEST(StructLiteralElaboration, PositionalStructLiteral) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  ab_t c;\n"
             "  initial c = '{8'hAA, 8'hBB};\n"
             "endmodule\n"));
}

TEST(StructLiteralElaboration, NamedMemberStructLiteral) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  ab_t c;\n"
             "  initial c = '{a: 8'h11, b: 8'h22};\n"
             "endmodule\n"));
}

TEST(StructLiteralElaboration, DefaultStructLiteral) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  ab_t c;\n"
             "  initial c = '{default: 8'hFF};\n"
             "endmodule\n"));
}

TEST(StructLiteralElaboration, TypePrefixedPattern) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] x; logic [7:0] y; } pt_t;\n"
             "  pt_t c;\n"
             "  initial c = pt_t'{x: 8'h05, y: 8'h0A};\n"
             "endmodule\n"));
}

TEST(StructLiteralElaboration, StructLiteralVarInit) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  ab_t c = '{8'h55, 8'hAA};\n"
             "endmodule\n"));
}

TEST(StructLiteralElaboration, InvalidMemberName) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s = "
      "'{nonexistent: 8'hFF};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StructLiteralElaboration, DuplicateMemberKey) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s = "
      "'{a: 8'h01, a: 8'h02};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StructLiteralElaboration, NestedBracesArrayOfStructs) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  ab_t arr [0:1];\n"
             "  initial arr = '{'{8'h11, 8'h22}, '{8'h33, 8'h44}};\n"
             "endmodule\n"));
}

TEST(StructLiteralElaboration, CLikeFlatLiteralForArrayOfStructsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a; shortreal b; } ab;\n"
      "  ab abarr[1:0] = '{1, 1.0, 2, 2.0};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(StructLiteralElaboration, ReplicationStructLiteral) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] x; logic [7:0] y; logic "
             "[7:0] z; } xyz_t;\n"
             "  xyz_t s;\n"
             "  initial s = '{3{8'hAA}};\n"
             "endmodule\n"));
}

}  // namespace
