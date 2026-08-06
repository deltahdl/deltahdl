#include <gtest/gtest.h>

#include "builders_ast.h"
#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "fixture_elaborator.h"
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
  EXPECT_TRUE(f.has_errors);
}

// The negative form: a variable index is not a constant expression, so the
// indexing select is not a static prefix and the longest static prefix is just
// the array identifier. That whole-array prefix overlaps the literal-indexed
// element, so the two processes are flagged as driving one target.
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
  EXPECT_TRUE(f.has_errors);
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
TEST(LongestStaticPrefixDriver, FieldSelectSameFieldConflicts) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  struct packed { logic [7:0] a; logic [7:0] b; } s;\n"
      "  always_comb s.a = 8'h1;\n"
      "  always_comb s.a = 8'h2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
TEST(LongestStaticPrefixDriver, ConstantExpressionIndexEvaluated) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:3];\n"
      "  always_comb arr[1 + 1] = 8'h1;\n"
      "  always_comb arr[2] = 8'h2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

// LRM example `m[i][1]`: a variable inner index makes the inner select
// non-static, so a constant outer index cannot extend the prefix and it
// collapses all the way to the array name `mem`, overlapping the element
// mem[0][0] driven by the other process.
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
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
