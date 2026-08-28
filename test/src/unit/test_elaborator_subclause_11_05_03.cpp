#include <gtest/gtest.h>

#include <string>

#include "builders_ast.h"
#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast.h"

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
  // A multi-level dotted reference (e.g. top.sub.sig) is a hierarchical
  // reference to an object; the whole chain is a static prefix.
  auto* sub = MakeMember(arena, MakeId(arena, "top"), "sub");
  auto* sig = MakeMember(arena, sub, "sig");
  EXPECT_EQ(LongestStaticPrefix(sig), "top.sub.sig");
}

TEST(LongestStaticPrefix, LongestStaticPrefixHierarchicalRefConstIdx) {
  Arena arena;
  // A constant index applied to a hierarchical reference stays inside the
  // static prefix.
  auto* mem =
      MakeMember(arena, MakeMember(arena, MakeId(arena, "top"), "sub"), "mem");
  auto* sel = MakeSelectExpr(arena, mem, MakeInt(arena, 2));
  EXPECT_EQ(LongestStaticPrefix(sel), "top.sub.mem[2]");
}

TEST(LongestStaticPrefix, LongestStaticPrefixHierarchicalRefVarIdx) {
  Arena arena;
  // A variable index breaks the static prefix back to the hierarchical name.
  auto* mem =
      MakeMember(arena, MakeMember(arena, MakeId(arena, "top"), "sub"), "mem");
  auto* sel = MakeSelectExpr(arena, mem, MakeId(arena, "i"));
  EXPECT_EQ(LongestStaticPrefix(sel), "top.sub.mem");
}

TEST(LongestStaticPrefix, LongestStaticPrefixVarThenConstIdx) {
  Arena arena;
  // LRM example: m[i][1]. The inner select is non-static, so a constant outer
  // index cannot extend the static prefix beyond the identifier.
  auto* inner = MakeSelectExpr(arena, MakeId(arena, "m"), MakeId(arena, "i"));
  auto* outer = MakeSelectExpr(arena, inner, MakeInt(arena, 1));
  EXPECT_EQ(LongestStaticPrefix(outer), "m");
}

TEST(LongestStaticPrefix, LongestStaticPrefixConstExprIdx) {
  Arena arena;
  // The select expression may be any constant expression, not just a literal.
  auto* idx =
      MakeBinary(arena, TokenKind::kPlus, MakeInt(arena, 1), MakeInt(arena, 1));
  auto* sel = MakeSelectExpr(arena, MakeId(arena, "m"), idx);
  EXPECT_EQ(LongestStaticPrefix(sel), "m[2]");
}

TEST(LongestStaticPrefix, LongestStaticPrefixIndexedPartSelectVarBase) {
  Arena arena;
  // An indexed part-select is an indexing select; with a base that can vary at
  // run time it is not a static prefix, so the prefix stops at the identifier.
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

// The tests below drive the longest-static-prefix rule end to end. Whether an
// indexing select is a static prefix turns on whether its index is a constant
// expression (§11.5.3), and that in turn depends on how the index identifier is
// declared -- a localparam/parameter is a constant form of §11.2.1, a variable
// is not. Rather than stub that distinction with a scope map, these build the
// declarations from real source and observe the rule through the place the
// elaborator applies it: the always_comb/always_latch/always_ff multi-driver
// check, which compares the longest static prefixes two processes drive. Two
// selects that resolve to distinct constant-indexed elements have disjoint
// prefixes and may be driven separately; a run-time index collapses the prefix
// to the whole array, so the two processes appear to over-drive one target.
//
// §11.5.3 prohibits nothing. Its opening sentence says the longest static
// prefix "is the longest part of the select for which an analysis tool has
// known values following elaboration", and its second sentence names where the
// concept is used: "This concept is used when describing implicit sensitivity
// lists (see 9.2.2.2) and when describing error conditions for drivers of logic
// ports (see 6.5)." Every rejection below is therefore reported under the rule
// the prefix is computed for -- §9.2.2.2 between two processes, and §10.3.2
// between a process and a continuous assignment -- and the subclause on the
// report is what tells one from the other.

// §11.2.1 literal index form: two literal-indexed elements are distinct static
// prefixes, so separate always_comb processes driving arr[0] and arr[1] do not
// conflict. This anchors the accepting path for the simplest constant form.
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

// §11.2.1 localparam index form: a localparam is a constant expression, so the
// indexing select stays in the static prefix and arr[A] / arr[B] name distinct
// elements. This is the case the empty-scope prefix computation previously got
// wrong -- collapsing both to "arr" and reporting a spurious multi-driver
// conflict.
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

// §11.2.1 parameter index form: a module parameter is likewise a constant
// expression and keeps the indexing select inside the static prefix.
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

// The constant index is genuinely evaluated, not treated opaquely: a localparam
// whose value equals another driver's literal index selects the same element,
// so the longest static prefixes coincide and the multi-driver conflict is
// (correctly) reported.
// The two prefixes coincide, so §9.2.2.2's single-driver rule is broken.
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

// The negative form: a variable index is not a constant expression, so the
// indexing select is not a static prefix and the longest static prefix is just
// the array identifier. That whole-array prefix overlaps the literal-indexed
// element, so the two processes are flagged as driving one target.
// The collapsed whole-array prefix overlaps, breaking §9.2.2.2.
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

// C2 / C5, field select from real struct syntax: `s.a` and `s.b` are field
// selects of the same static prefix `s` but name different fields, so their
// longest static prefixes are distinct and two processes may drive them
// separately. The struct operand is built from an actual declaration rather
// than a hand-assembled member-access node.
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

// C2, the accepting field select must still collide with itself: two processes
// driving the same field `s.a` share one longest static prefix and are a real
// multi-driver conflict.
// One shared field prefix, so §9.2.2.2 reports the conflict.
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

// C3, non-indexed part-select (a form of indexing select): its bounds are
// constant, so `vect[3:0]` and `vect[7:4]` are distinct static prefixes and the
// two processes drive disjoint bit ranges without conflict.
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

// C3 / C6, indexed part-select whose base can vary at run time: the base is not
// a constant expression, so the part-select is not a static prefix and the
// longest static prefix collapses to `vect`, overlapping the constant-bounded
// part-select of the other process. The variable base comes from a real
// variable declaration, not a stubbed scope.
// The collapsed prefix overlaps the constant-bounded one, breaking §9.2.2.2.
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

// C3, the descending indexed part-select (`-:`) is another indexing-select
// form. With constant bases it stays in the static prefix, so `vect[7 -: 4]`
// and `vect[3 -: 4]` are distinct prefixes over disjoint bit ranges and do not
// conflict. This exercises the `-:` syntactic form end to end alongside the
// ascending `+:` case above.
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

// C6, the select expression may be any constant expression, including an
// operator expression over constants -- a different evaluation path than a bare
// literal or a named constant. `arr[1+1]` evaluates to element 2, so it shares
// a longest static prefix with `arr[2]` and the two drivers conflict; this
// proves the constant expression is actually evaluated, not treated opaquely.
// Both selects reach element 2, so §9.2.2.2 reports one over-driven target.
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

// The longest-static-prefix rule also governs a continuous-assignment left-hand
// side (a distinct syntactic position from a procedural assignment, resolved
// through a separate collection path). A localparam bit-select index is a
// constant expression, so `assign v[P]` with P=0 has prefix `v[0]`, disjoint
// from the `always_comb`-driven bit `v[1]`; the two drivers do not conflict.
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

// Negative form for the continuous-assignment position: when the localparam
// index resolves to the same bit the procedural process drives (P=1), the two
// longest static prefixes coincide and the process-versus-continuous-assign
// conflict is reported. This also confirms the parameter is resolved on the
// continuous-assignment collection path, not just the procedural one.
// The rule broken is §10.3.2's, not §9.2.2.2's, because one of the two drivers
// is a continuous assignment rather than a process.
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

// The following three build the worked examples of this subclause from real
// multidimensional array syntax (the §11.5.2 array-addressing dependency) and
// drive them through elaboration, observing the resulting longest static prefix
// via the multi-driver check.

// LRM example `m[p][1]`: with both indices constant (a localparam and a
// literal) the whole select is a static prefix, so mem[P][1] and mem[1][2] name
// different elements and do not conflict.
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

// LRM example `m[1][i]`: a constant inner index with a variable outer index
// yields prefix mem[1] -- the whole row. That row prefix contains the specific
// element mem[1][2] driven by the other process, so the two conflict.
// The row prefix contains the element the other process drives, breaking
// §9.2.2.2.
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

// LRM example `m[i][1]`: a variable inner index makes the inner select
// non-static, so a constant outer index cannot extend the prefix and it
// collapses all the way to the array name `mem`, overlapping the element
// mem[0][0] driven by the other process.
// The prefix collapses to the array name and overlaps, breaking §9.2.2.2.
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

// The five cases below cover the statement positions CollectStmtLhsPrefixes in
// src/elaborator/elaborator_process.cpp reaches only since it took its list of
// nested statements from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. It had written out nine of the
// thirteen child-statement links Stmt declares, and a longest static prefix it
// never gathered is a driver nothing knows about: the target below was driven
// by an always_comb and by an initial procedure at once, and every one of these
// sources elaborated clean.
//
// `stmt` stands in the initial procedure, so the prefix it contributes reaches
// the rule through the general procedural driver set alone, which is what
// CollectStmtLhsPrefixes fills. §9.2.2.2 is the rule reported, its "shall not
// be assigned by any other process" being what the always_comb and the initial
// procedure break between them, and §11.5.3 is what makes the report name the
// bit `v[0]` rather than the whole vector `v`.
//
// The report stands at the always_comb, which is line 4 of every source built
// here whatever `stmt` runs to, and the line is read back out of the source
// rather than counted so that it stays right if the preamble is edited.
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

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each. §9.2.2.2 counts an assignment as a driver whether it
// runs on a given pass or not, so the arm the assertion would take is not the
// question.
TEST(LongestStaticPrefixDriver, ElementAssignedInAnAssertionPassStmtIsADriver) {
  ExpectElementDrivenByInitialStmt("assert (ok) v[0] = 1'b0;");
}

TEST(LongestStaticPrefixDriver, ElementAssignedInAnAssertionFailStmtIsADriver) {
  ExpectElementDrivenByInitialStmt("assert (ok) else v[0] = 1'b0;");
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. The weighted draw picks an item while the design runs; the
// single-driver rule is decided before it does, so an item is a driver whether
// it would be selected or not.
TEST(LongestStaticPrefixDriver, ElementAssignedInARandcaseItemIsADriver) {
  ExpectElementDrivenByInitialStmt("randcase 1: v[0] = 1'b0; endcase");
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(LongestStaticPrefixDriver,
     ElementAssignedInARandsequenceCodeBlockIsADriver) {
  ExpectElementDrivenByInitialStmt(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { v[0] = 1'b0; };\n"
      "      endsequence\n"
      "    end");
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second statement list
// under Stmt::rs_productions, reached by a different member from
// RsProd::code_stmts, so the case above does not answer for it.
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

}  // namespace
