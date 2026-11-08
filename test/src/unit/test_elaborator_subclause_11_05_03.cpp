#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "builders_ast.h"
#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

using namespace delta;

namespace {

Expr* MakeMember(Arena& arena, Expr* obj, std::string_view field) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kMemberAccess;
  e->lhs = obj;
  e->rhs = MakeId(arena, field);
  return e;
}

TEST(LongestStaticPrefix, LongestStaticPrefixNullExpr) {
  EXPECT_EQ(LongestStaticPrefix(nullptr), "");
}

TEST(LongestStaticPrefix, LongestStaticPrefixNonSelectExpr) {
  Arena arena;
  auto* bin = MakeBinary(arena, TokenKind::kPlus, MakeId(arena, "a"),
                         MakeId(arena, "b"));
  EXPECT_EQ(LongestStaticPrefix(bin), "");
}

TEST(LongestStaticPrefix, LongestStaticPrefixAllConstMultiDim) {
  Arena arena;
  auto* inner = MakeSelectExpr(arena, MakeId(arena, "m"), MakeInt(arena, 1));
  auto* outer = MakeSelectExpr(arena, inner, MakeInt(arena, 2));
  EXPECT_EQ(LongestStaticPrefix(outer), "m[1][2]");
}

TEST(LongestStaticPrefix, LongestStaticPrefixAllVarMultiDim) {
  Arena arena;
  auto* inner = MakeSelectExpr(arena, MakeId(arena, "m"), MakeId(arena, "i"));
  auto* outer = MakeSelectExpr(arena, inner, MakeId(arena, "j"));
  EXPECT_EQ(LongestStaticPrefix(outer), "m");
}

TEST(LongestStaticPrefix, LongestStaticPrefixSimpleId) {
  Arena arena;

  EXPECT_EQ(LongestStaticPrefix(MakeId(arena, "m")), "m");
}

TEST(LongestStaticPrefix, LongestStaticPrefixConstIdx) {
  Arena arena;

  auto* sel = MakeSelectExpr(arena, MakeId(arena, "m"), MakeInt(arena, 1));
  EXPECT_EQ(LongestStaticPrefix(sel), "m[1]");
}

TEST(LongestStaticPrefix, LongestStaticPrefixVarIdx) {
  Arena arena;

  auto* sel = MakeSelectExpr(arena, MakeId(arena, "m"), MakeId(arena, "i"));
  EXPECT_EQ(LongestStaticPrefix(sel), "m");
}

TEST(LongestStaticPrefix, LongestStaticPrefixNested) {
  Arena arena;

  auto* inner = MakeSelectExpr(arena, MakeId(arena, "m"), MakeInt(arena, 1));
  auto* outer = MakeSelectExpr(arena, inner, MakeId(arena, "i"));
  EXPECT_EQ(LongestStaticPrefix(outer), "m[1]");
}

TEST(LongestStaticPrefix, LongestStaticPrefixFieldSelect) {
  Arena arena;
  auto* expr = MakeMember(arena, MakeId(arena, "s"), "field");
  EXPECT_EQ(LongestStaticPrefix(expr), "s.field");
}

TEST(LongestStaticPrefix, LongestStaticPrefixFieldSelectThenConstIdx) {
  Arena arena;
  auto* field = MakeMember(arena, MakeId(arena, "s"), "field");
  auto* sel = MakeSelectExpr(arena, field, MakeInt(arena, 1));
  EXPECT_EQ(LongestStaticPrefix(sel), "s.field[1]");
}

TEST(LongestStaticPrefix, LongestStaticPrefixConstIdxThenFieldSelect) {
  Arena arena;
  auto* sel = MakeSelectExpr(arena, MakeId(arena, "arr"), MakeInt(arena, 1));
  auto* expr = MakeMember(arena, sel, "field");
  EXPECT_EQ(LongestStaticPrefix(expr), "arr[1].field");
}

TEST(LongestStaticPrefix, LongestStaticPrefixVarIdxThenFieldSelect) {
  Arena arena;
  auto* sel = MakeSelectExpr(arena, MakeId(arena, "arr"), MakeId(arena, "i"));
  auto* expr = MakeMember(arena, sel, "field");
  EXPECT_EQ(LongestStaticPrefix(expr), "arr");
}

TEST(LongestStaticPrefix, LongestStaticPrefixHierarchicalRef) {
  Arena arena;
  auto* sub = MakeMember(arena, MakeId(arena, "top"), "sub");
  auto* sig = MakeMember(arena, sub, "sig");
  EXPECT_EQ(LongestStaticPrefix(sig), "top.sub.sig");
}

TEST(LongestStaticPrefix, LongestStaticPrefixHierarchicalRefConstIdx) {
  Arena arena;
  auto* mem =
      MakeMember(arena, MakeMember(arena, MakeId(arena, "top"), "sub"), "mem");
  auto* sel = MakeSelectExpr(arena, mem, MakeInt(arena, 2));
  EXPECT_EQ(LongestStaticPrefix(sel), "top.sub.mem[2]");
}

TEST(LongestStaticPrefix, LongestStaticPrefixHierarchicalRefVarIdx) {
  Arena arena;
  auto* mem =
      MakeMember(arena, MakeMember(arena, MakeId(arena, "top"), "sub"), "mem");
  auto* sel = MakeSelectExpr(arena, mem, MakeId(arena, "i"));
  EXPECT_EQ(LongestStaticPrefix(sel), "top.sub.mem");
}

TEST(LongestStaticPrefix, LongestStaticPrefixVarThenConstIdx) {
  Arena arena;
  auto* inner = MakeSelectExpr(arena, MakeId(arena, "m"), MakeId(arena, "i"));
  auto* outer = MakeSelectExpr(arena, inner, MakeInt(arena, 1));
  EXPECT_EQ(LongestStaticPrefix(outer), "m");
}

TEST(LongestStaticPrefix, LongestStaticPrefixConstExprIdx) {
  Arena arena;
  auto* idx =
      MakeBinary(arena, TokenKind::kPlus, MakeInt(arena, 1), MakeInt(arena, 1));
  auto* sel = MakeSelectExpr(arena, MakeId(arena, "m"), idx);
  EXPECT_EQ(LongestStaticPrefix(sel), "m[2]");
}

TEST(LongestStaticPrefix, LongestStaticPrefixIndexedPartSelectVarBase) {
  Arena arena;
  auto* sel = MakeSelectExpr(arena, MakeId(arena, "arr"), MakeId(arena, "i"));
  sel->index_end = MakeInt(arena, 4);
  sel->is_part_select_plus = true;
  EXPECT_EQ(LongestStaticPrefix(sel), "arr");
}

TEST(LongestStaticPrefix, LongestStaticPrefixPackageRef) {
  Arena arena;
  auto* id = MakeId(arena, "var");
  id->scope_prefix = "pkg::";
  EXPECT_EQ(LongestStaticPrefix(id), "pkg::var");
}

TEST(LongestStaticPrefix, LongestStaticPrefixPackageRefConstIdx) {
  Arena arena;
  auto* id = MakeId(arena, "arr");
  id->scope_prefix = "pkg::";
  auto* sel = MakeSelectExpr(arena, id, MakeInt(arena, 3));
  EXPECT_EQ(LongestStaticPrefix(sel), "pkg::arr[3]");
}

TEST(LongestStaticPrefixDriver, LiteralIndexDistinctElementsNoConflict) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:3];\n"
      "  always_comb arr[0] = 8'h1;\n"
      "  always_comb arr[1] = 8'h2;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(LongestStaticPrefixDriver, LocalparamIndexDistinctElementsNoConflict) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  localparam A = 0;\n"
      "  localparam B = 1;\n"
      "  logic [7:0] arr [0:3];\n"
      "  always_comb arr[A] = 8'h1;\n"
      "  always_comb arr[B] = 8'h2;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(LongestStaticPrefixDriver, ParameterIndexDistinctElementsNoConflict) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter P = 2)(input logic clk);\n"
      "  logic [7:0] arr [0:3];\n"
      "  always_comb arr[P] = 8'h1;\n"
      "  always_comb arr[3] = 8'h2;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(LongestStaticPrefixDriver, ConstantIndexSameElementConflicts) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  localparam P = 1;\n"
      "  logic [7:0] arr [0:3];\n"
      "  always_comb arr[P] = 8'h1;\n"
      "  always_comb arr[1] = 8'h2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "driven by multiple always_comb/always_latch/always_ff", 5, "9.2.2.2"));
}

TEST(LongestStaticPrefixDriver, VariableIndexCollapsesToBaseConflicts) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:3];\n"
      "  int i;\n"
      "  always_comb arr[i] = 8'h1;\n"
      "  always_comb arr[1] = 8'h2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "driven by multiple always_comb/always_latch/always_ff", 5, "9.2.2.2"));
}

TEST(LongestStaticPrefixDriver, FieldSelectDistinctFieldsNoConflict) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s;\n"
      "  always_comb s.a = 8'h1;\n"
      "  always_comb s.b = 8'h2;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(LongestStaticPrefixDriver, FieldSelectSameFieldConflicts) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s;\n"
      "  always_comb s.a = 8'h1;\n"
      "  always_comb s.a = 8'h2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "driven by multiple always_comb/always_latch/always_ff", 4, "9.2.2.2"));
}

TEST(LongestStaticPrefixDriver, PartSelectDistinctRangesNoConflict) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] vect;\n"
      "  always_comb vect[3:0] = 4'h1;\n"
      "  always_comb vect[7:4] = 4'h2;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(LongestStaticPrefixDriver, IndexedPartSelectVariableBaseConflicts) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] vect;\n"
      "  int i;\n"
      "  always_comb vect[i +: 4] = 4'h1;\n"
      "  always_comb vect[3:0] = 4'h2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "driven by multiple always_comb/always_latch/always_ff", 5, "9.2.2.2"));
}

TEST(LongestStaticPrefixDriver,
     DescendingIndexedPartSelectConstantBaseNoConflict) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] vect;\n"
      "  always_comb vect[7 -: 4] = 4'h1;\n"
      "  always_comb vect[3 -: 4] = 4'h2;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(LongestStaticPrefixDriver, ConstantExpressionIndexEvaluated) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:3];\n"
      "  always_comb arr[1 + 1] = 8'h1;\n"
      "  always_comb arr[2] = 8'h2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "driven by multiple always_comb/always_latch/always_ff", 4, "9.2.2.2"));
}

TEST(LongestStaticPrefixDriver,
     ContinuousAssignConstantIndexDistinctBitsNoConflict) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  localparam P = 0;\n"
      "  logic [7:0] v;\n"
      "  assign v[P] = 1'b1;\n"
      "  always_comb v[1] = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(LongestStaticPrefixDriver, ContinuousAssignConstantIndexSameBitConflicts) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  localparam P = 1;\n"
      "  logic [7:0] v;\n"
      "  assign v[P] = 1'b1;\n"
      "  always_comb v[1] = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "driven by always_comb and continuous assignment",
                            5, "10.3.2"));
}

TEST(LongestStaticPrefixDriver, MultiDimConstantIndicesWholeSelectStatic) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  localparam P = 0;\n"
      "  logic [7:0] mem [0:3][0:3];\n"
      "  always_comb mem[P][1] = 8'h1;\n"
      "  always_comb mem[1][2] = 8'h2;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(LongestStaticPrefixDriver, MultiDimVariableOuterIndexStopsAtRow) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] mem [0:3][0:3];\n"
      "  int i;\n"
      "  always_comb mem[1][i] = 8'h1;\n"
      "  always_comb mem[1][2] = 8'h2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "driven by multiple always_comb/always_latch/always_ff", 5, "9.2.2.2"));
}

TEST(LongestStaticPrefixDriver, MultiDimVariableInnerIndexCollapsesToBase) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] mem [0:3][0:3];\n"
      "  int i;\n"
      "  always_comb mem[i][1] = 8'h1;\n"
      "  always_comb mem[0][0] = 8'h2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "driven by multiple always_comb/always_latch/always_ff", 5, "9.2.2.2"));
}

void ExpectElementDrivenByInitialStmt(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n"
      "  logic [7:0] v;\n"
      "  logic ok;\n"
      "  always_comb v[0] = 1'b1;\n"
      "  initial\n"
      "    " +
      stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "variable 'v[0]' driven by always_comb and another process",
                    LineHolding(src, "always_comb"), "9.2.2.2"));
}

TEST(LongestStaticPrefixDriver, ElementAssignedInAnAssertionPassStmtIsADriver) {
  ExpectElementDrivenByInitialStmt("assert (ok) v[0] = 1'b0;");
}

TEST(LongestStaticPrefixDriver, ElementAssignedInAnAssertionFailStmtIsADriver) {
  ExpectElementDrivenByInitialStmt("assert (ok) else v[0] = 1'b0;");
}

TEST(LongestStaticPrefixDriver, ElementAssignedInARandcaseItemIsADriver) {
  ExpectElementDrivenByInitialStmt("randcase 1: v[0] = 1'b0; endcase");
}

TEST(LongestStaticPrefixDriver,
     ElementAssignedInARandsequenceCodeBlockIsADriver) {
  ExpectElementDrivenByInitialStmt(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { v[0] = 1'b0; };\n"
      "      endsequence\n"
      "    end");
}

TEST(LongestStaticPrefixDriver,
     ElementAssignedInARandsequenceWeightCodeBlockIsADriver) {
  ExpectElementDrivenByInitialStmt(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { v[0] = 1'b0; };\n"
      "        alt : { ok = 1'b1; };\n"
      "      endsequence\n"
      "    end");
}

TEST(LongestStaticPrefixElaboration, OverlappingPartSelectDriversReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] v, u;\n"
      "  logic a, b;\n"
      "  always_comb v[7:4] = {4{a}};\n"
      "  always_comb v[5] = b;\n"
      "  always_comb u[3:0] = {4{a}};\n"
      "  always_comb u[4 +: 4] = {4{b}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "driven by multiple always_comb/always_latch/always_ff", 5, "9.2.2.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(LongestStaticPrefixElaboration, OverlappingIndexedPartSelectReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] v;\n"
      "  logic a, b;\n"
      "  always_comb v[7:4] = {4{a}};\n"
      "  always_comb v[4 -: 4] = {4{b}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "driven by multiple always_comb/always_latch/always_ff", 5, "9.2.2.2"));
}

}  // namespace
