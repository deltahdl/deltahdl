#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'nonexistent' is not a member of the struct", 2,
                            "10.9.2"));
}

TEST(StructLiteralElaboration, DuplicateMemberKey) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s = "
      "'{a: 8'h01, a: 8'h02};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "duplicate member key 'a' in pattern", 2,
                            "10.9.2"));
}

TEST(StructLiteralElaboration, NestedBracesArrayOfStructs) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  ab_t arr [0:1];\n"
             "  initial arr = '{'{8'h11, 8'h22}, '{8'h33, 8'h44}};\n"
             "endmodule\n"));
}

// §5.10 (printed page 84) has the nested braces of a structure literal reflect
// the structure, names the C-like flat alternative of its own two-element
// example as not allowed, and has the braces of an initialized array of
// structures reflect the array and the structure. The flat form is what the
// spelling breaks, so the report is §5.10's, not the §10.9.1 element count
// that flattening two two-member structures into a two-element array also
// fails.
TEST(StructLiteralElaboration, CLikeFlatLiteralForArrayOfStructsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a; shortreal b; } ab;\n"
      "  ab abarr[1:0] = '{1, 1.0, 2, 2.0};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern for an array of structures "
                            "shall nest a pattern per structure",
                            3, "5.10"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "assignment pattern has 4 elements", 3, "10.9.1"));
}

// The module of 5.10-structure-arrays-illegal.sv, whose rejection is scored
// against §5.10: the same flat form, and no §10.9.2 report for it, since the
// pattern initializes an array, not a structure.
TEST(StructLiteralElaboration, FlatLiteralForStructArrayIsReportedUnder510) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef struct {\n"
      "    int a;\n"
      "    int b;\n"
      "  } ms_t;\n"
      "\n"
      "  /* C-like assignment is illegal */\n"
      "  ms_t ms[1:0] = '{0, 0, 1, 1};\n"
      "\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern for an array of structures "
                            "shall nest a pattern per structure",
                            8, "5.10"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "positional struct pattern has 4 elements", 8,
                             "10.9.2"));
}

// The flat form whose count happens to agree with the array's: two literals
// for two structures is still no nesting, and only the type of each element
// tells it from the nested form.
TEST(StructLiteralElaboration, CountAgreeingFlatLiteralForStructArrayRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a; int b; } ab;\n"
      "  ab abarr[1:0] = '{0, 0};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern for an array of structures "
                            "shall nest a pattern per structure",
                            3, "5.10"));
}

// A structure variable per element is the nesting the clause asks for,
// written through names rather than braces.
TEST(StructLiteralElaboration, StructVariablesPerElementOfStructArrayAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct { int a; int b; } ab;\n"
             "  ab s1 = '{1, 2};\n"
             "  ab s2 = '{3, 4};\n"
             "  ab abarr[1:0] = '{s1, s2};\n"
             "endmodule\n"));
}

// §7.2.1 has a packed structure take an integral value as a whole, so a
// literal per element of an array of packed structures is no flat form.
TEST(StructLiteralElaboration, LiteralPerElementOfPackedStructArrayAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab;\n"
             "  ab abarr[1:0] = '{16'h0102, 16'h0304};\n"
             "endmodule\n"));
}

// The nested form at a declaration, with an array extent that differs from
// the member count: the pattern is an array pattern, so the structure's
// member count has nothing to say about how many elements it lists.
TEST(StructLiteralElaboration,
     NestedPatternsForThreeElementStructArrayAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct { int a; int b; } ab;\n"
             "  ab abarr[2:0] = '{'{0, 1}, '{2, 3}, '{4, 5}};\n"
             "endmodule\n"));
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
