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

TEST(StructLiteralElaboration,
     FlatLiteralForStructArrayIsReportedAsAStructureLiteral) {
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

TEST(StructLiteralElaboration, StructVariablesPerElementOfStructArrayAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct { int a; int b; } ab;\n"
             "  ab s1 = '{1, 2};\n"
             "  ab s2 = '{3, 4};\n"
             "  ab abarr[1:0] = '{s1, s2};\n"
             "endmodule\n"));
}

TEST(StructLiteralElaboration, LiteralPerElementOfPackedStructArrayAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab;\n"
             "  ab abarr[1:0] = '{16'h0102, 16'h0304};\n"
             "endmodule\n"));
}

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

TEST(StructLiteralElaboration, ReplicationSupplyingTooManyMembersRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  struct { int a; int b; } s = '{3{1}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "replication supplies 3 values, but struct has 2 "
                            "members",
                            2, "5.10"));
}

TEST(StructLiteralElaboration,
     ReplicationOfSeveralItemsFillingMembersAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  struct { int a; int b; int c; int d; } s = '{2{1, 2}};\n"
             "endmodule\n"));
}

TEST(StructLiteralElaboration, FlatLiteralOutsideModuleDeclarationRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a; shortreal b; } ab;\n"
      "  ab abarr [1:0];\n"
      "  initial abarr = '{1, 1.0, 2, 2.0};\n"
      "  initial begin\n"
      "    ab local_arr [1:0] = '{1, 1.0, 2, 2.0};\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kMessage =
      "assignment pattern for an array of structures shall nest a pattern per "
      "structure";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 4, "5.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 6, "5.10"));
}

TEST(StructLiteralElaboration, FlatLiteralForTypedefArrayOfStructsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a; shortreal b; } ab;\n"
      "  typedef ab ab2_t [1:0];\n"
      "  ab2_t abarr = '{1, 1.0, 2, 2.0};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern for an array of structures "
                            "shall nest a pattern per structure",
                            4, "5.10"));
}

TEST(StructLiteralElaboration, ReplicationFillingAnArrayMemberAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  struct { int a; int b[4]; } s = '{1, '{2{2, 3}}};\n"
             "endmodule\n"));
}

}  // namespace
