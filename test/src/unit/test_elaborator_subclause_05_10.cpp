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

// §5.10 opens "Structure literals are structure assignment patterns or pattern
// expressions with constant member expressions (see 10.9.2)", so it states no
// member-key rule of its own and the report names §10.9.2, where the rule is.
TEST(StructLiteralElaboration, InvalidMemberName) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s = "
      "'{nonexistent: 8'hFF};\n"
      "endmodule\n",
      f);
  const Diagnostic* diag =
      FindDiag(f, "'nonexistent' is not a member of the struct");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "10.9.2");
}

TEST(StructLiteralElaboration, DuplicateMemberKey) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s = "
      "'{a: 8'h01, a: 8'h02};\n"
      "endmodule\n",
      f);
  const Diagnostic* diag = FindDiag(f, "duplicate member key 'a' in pattern");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "10.9.2");
}

TEST(StructLiteralElaboration, NestedBracesArrayOfStructs) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  ab_t arr [0:1];\n"
             "  initial arr = '{'{8'h11, 8'h22}, '{8'h33, 8'h44}};\n"
             "endmodule\n"));
}

// §5.10: "Nested braces shall reflect the structure", and of this very example
// the standard says "The C-like alternative '{1, 1.0, 2, 2.0} for the preceding
// example is not allowed." What rejects it here is the §10.9.1 element count,
// since flattening two two-member structures offers four elements to a
// two-element array. §5.10 also forbids the flat form when the counts happen to
// agree, and that narrower rule has no report: deciding it needs the type of
// each element expression, which this pass does not carry, and a check written
// without it would reject the legal '{s1, s2} of two struct variables.
TEST(StructLiteralElaboration, CLikeFlatLiteralForArrayOfStructsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a; shortreal b; } ab;\n"
      "  ab abarr[1:0] = '{1, 1.0, 2, 2.0};\n"
      "endmodule\n",
      f);
  const Diagnostic* diag = FindDiag(
      f, "assignment pattern has 4 elements, but array dimension requires 2");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "10.9.1");
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
