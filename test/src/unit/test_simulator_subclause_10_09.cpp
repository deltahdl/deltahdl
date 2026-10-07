#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_string_var.h"
#include "parser/ast_expr.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(AssignmentPatternSimulation, PositionalTwoElements) {
  SimFixture f;
  auto* a = f.ctx.CreateVariable("a", 8);
  auto* b = f.ctx.CreateVariable("b", 8);
  a->value = MakeLogic4VecVal(f.arena, 8, 5);
  b->value = MakeLogic4VecVal(f.arena, 8, 10);
  auto* expr = ParseExprFrom("'{a, b}", f);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kAssignmentPattern);
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0x050Au);
}

TEST(AssignmentPatternSimulation, PositionalThreeElements) {
  SimFixture f;
  auto* a = f.ctx.CreateVariable("a", 4);
  auto* b = f.ctx.CreateVariable("b", 4);
  auto* c = f.ctx.CreateVariable("c", 4);
  a->value = MakeLogic4VecVal(f.arena, 4, 1);
  b->value = MakeLogic4VecVal(f.arena, 4, 2);
  c->value = MakeLogic4VecVal(f.arena, 4, 3);
  auto* expr = ParseExprFrom("'{a, b, c}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.width, 12u);
  EXPECT_EQ(result.ToUint64(), 0x123u);
}

TEST(AssignmentPatternSimulation, SingleElement) {
  SimFixture f;
  auto* a = f.ctx.CreateVariable("a", 32);
  a->value = MakeLogic4VecVal(f.arena, 32, 42);
  auto* expr = ParseExprFrom("'{a}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(AssignmentPatternSimulation, EmptyPatternRejectedBeforeEvaluation) {
  SimFixture f;
  ParseExprFrom("'{}", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern needs at least one expression",
                            1, "10.9"));
}

TEST(AssignmentPatternSimulation, SizedLiterals) {
  SimFixture f;
  auto* expr = ParseExprFrom("'{32'd5, 32'd10}", f);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kAssignmentPattern);
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.width, 64u);
  uint64_t expected = (uint64_t{5} << 32) | 10;
  EXPECT_EQ(result.ToUint64(), expected);
}

TEST(AssignmentPatternSimulation, ReplicationPatternEvaluates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x = '{4{8'hAB}};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABABABABu);
}

TEST(AssignmentPatternSimulation, IntegerAtomTypePatternEvaluates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = int'{42};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(AssignmentPatternSimulation, LhsPositionalUnpackingTwoElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    '{a, b} = 16'hABCD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0xABu);
  EXPECT_EQ(vb->value.ToUint64(), 0xCDu);
}

// §10.9: an assignment pattern expression (a pattern with a data-type prefix)
// is also legal as a left-hand target. With the required positional notation it
// unpacks the right-hand value across its members MSB-first, exactly as the
// bare pattern it wraps would. The type prefix only names the aggregate; it
// does not alter the slicing. Here 16'hABCD splits into a=0xAB (high byte),
// b=0xCD.
//
// The EXPECT_FALSE(f.has_errors) is what makes this case about the typed
// spelling at all, and it is the only assertion here that can be. §10.9 obliges
// each member expression to have as many bits as the matching element of the
// assignment pattern expression's data type, so the bare `'{a, b}` slices
// 16'hABCD into exactly the bytes `pair_t'{a, b}` does, and
// LhsPositionalUnpackingTwoElements above already runs that spelling on the
// same two values. When the type prefix was mistaken for the data type of a
// §6.8 declaration, the two reports left the position on the `'{` and the
// block's loop reparsed the bare pattern, which answered a=0xAB and b=0xCD as
// before; ElaborateSrc returns the design whatever the diagnostics say, so
// ASSERT_NE(design, nullptr) survived that too. Reading the values back is
// therefore what this case has in common with the bare-pattern one, and reading
// the diagnostics is what distinguishes them.
TEST(AssignmentPatternSimulation, TypedLhsPatternUnpacks) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    pair_t'{a, b} = 16'hABCD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0xABu);
  EXPECT_EQ(vb->value.ToUint64(), 0xCDu);
}

TEST(AssignmentPatternSimulation, ByteTypePrefixEvaluates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte b;\n"
      "  initial begin\n"
      "    b = byte'{8'd42};\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §10.9: an assignment pattern expression whose prefix is a type reference
// (type(x)'{...}) has the self-determined type of that reference and, used on
// the right-hand side, yields the value a variable of it would hold. type(x) is
// logic[15:0] here, so the two bytes pack MSB-first into 0x0102.
TEST(AssignmentPatternSimulation, TypeReferencePrefixYieldsValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    x = type(x)'{8'd1, 8'd2};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0102u);
}

// §10.9: an assignment pattern expression whose prefix is a named (ps_type)
// aggregate type yields, on the right-hand side, the value a variable of that
// type would hold if initialized with the pattern. A positional pair_t pattern
// packs its members in declaration order: a=0x12 (high byte), b=0x34.
TEST(AssignmentPatternSimulation, StructTypePrefixYieldsValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p = pair_t'{8'h12, 8'h34};\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x1234u);
}

// §10.9: an assignment pattern expression (a pattern carrying a data-type
// prefix) has a self-determined data type, so unlike a bare assignment pattern
// it is not restricted to being one whole side of an assignment-like context.
// When it appears as an operand inside a larger right-hand expression it shall
// yield the value a variable of that type would hold if initialized with the
// pattern: int'{40} yields 40, so the sum is 42. The companion elaborator test
// only confirms this composes without error; here the runtime value is
// observed.
TEST(AssignmentPatternSimulation, TypedPatternExpressionAsOperandYieldsValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = int'{40} + 2;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(AssignmentPatternSimulation, PositionalPatternYieldsCorrectValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    x = '{8'hAB, 8'hCD};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

TEST(AssignmentPatternSimulation, SingleElementPositionalPattern) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = '{8'd42};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(AssignmentPatternSimulation, FourElementPositionalPattern) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x = '{8'd1, 8'd2, 8'd3, 8'd4};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x01020304u);
}

TEST(AssignmentPatternSimulation, PatternInConditionalBranch) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    if (1) x = '{8'd5, 8'd6};\n"
      "    else x = '{8'd0, 8'd0};\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1286u);
}

TEST(AssignmentPatternSimulation, PatternInCaseItemBody) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sel;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    case(sel)\n"
      "      8'd0: x = '{8'd0, 8'd0};\n"
      "      8'd1: x = '{8'd10, 8'd20};\n"
      "      default: x = '{8'd0, 8'd0};\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 2580u);
}

TEST(AssignmentPatternSimulation, PatternInForLoop) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial begin\n"
      "    x = 16'd0;\n"
      "    for (int i = 0; i < 3; i = i + 1) begin\n"
      "      x = '{8'd7, 8'd8};\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1800u);
}

// §10.9: an assignment pattern may also be positional, with no keys, and it
// pairs a collection of expressions with the fields and elements of a data
// object. §10.10.3 writes one whose expressions are string literals and says
// what the correspondence leaves behind:
//
//   SQ = '{"element 0", "element 1"};   // assignment pattern, two strings
//
// Every element is checked, not just the count and not just one of them. The
// pattern's items reach the queue by two different routes -- the first is the
// one the parser must decide between an item and a key, the rest have no such
// question -- so a run that stored one item and lost the other holds the right
// number of elements and answers a size check exactly as a correct one does.
TEST(AssignmentPatternSimulation, PositionalStringLiteralsSeedAStringQueue) {
  RunAndExpectStringQueue(
      "module t;\n"
      "  string SQ[$];\n"
      "  initial SQ = '{\"element 0\", \"element 1\"};\n"
      "endmodule\n",
      "SQ", {"element 0", "element 1"});
}

// §10.9.1: an unpacked array assigned from a concatenation takes one element
// per entry, so a concatenation of the wrong length is reported. The design
// makes two such assignments and only the second one is the wrong length, so a
// report carrying no location fails this and so does one that names the first.
TEST(AssignmentPatternSimulation, SizeMismatchIsReportedAtTheConcatenation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a [0:2];\n"
      "  int b [0:2];\n"
      "  initial begin\n"
      "    a = {1, 2, 3};\n"
      "    b = {1, 2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation size mismatch", 6,
                            "10.10"));
}

// §10.9 (printed page 261): an assignment pattern expression is the value a
// variable of its type holds once initialized with the pattern, and the
// clause's own `shortint'({T'{1,2}, T'{3,4}})` yields 16'h1234, so each item
// of a pattern for a packed array fills one element at the element's width.
// §10.9.1 fills a packed array assigned an untyped pattern the same way, and
// an item that is itself a pattern fills its element over the next dimension.
// Concatenated at the items' own 32 bits and cut to the target's width, only
// the last item survived: 8'h02, 8'h04, 24'h000003, 16'h0204.
TEST(AssignmentPatternSim, PackedArrayPatternFillsEachElement) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef logic [1:0][3:0] T;\n"
      "  logic [7:0] z; logic [1:0][3:0] x; logic [2:0][7:0] y;\n"
      "  shortint v; logic [1:0][1:0][3:0] w;\n"
      "  initial begin\n"
      "    z = T'{1,2}; x = '{3,4}; y = '{8'h1, 2, 3};\n"
      "    v = shortint'({T'{1,2}, T'{3,4}});\n"
      "    w = '{'{1,2}, '{3,4}};\n"
      "    $display(\"%h %h %h %h %h\", z, x, y, v, w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "12 34 010203 1234 1234\n");
}

// §10.9 (printed page 261), the clause's own example: an assignment pattern on
// the left deconstructs an unpacked array, each member taking one element and
// the first member the leftmost, and a pattern on the right is evaluated whole
// before any member is written, so `U'{c, a, b} = '{a+1, b+1, c+1}` leaves c,
// a and b the sums 2, 3 and 4. A queue deconstructs the same way, and so does
// the array into its own elements, which a member-by-member copy that read
// an element after writing it would get wrong. Cut as a packed concatenation,
// only the last member received anything: `0 0 3` and `0 4 0`.
TEST(AssignmentPatternSim, PatternTargetDeconstructsAnUnpackedArray) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef byte U[3];\n"
      "  U A = '{1, 2, 3}; byte a, b, c; int q[$] = '{7, 8, 9};\n"
      "  initial begin\n"
      "    U'{a, b, c} = A; $display(\"%0d %0d %0d\", a, b, c);\n"
      "    U'{c, a, b} = '{a+1, b+1, c+1};\n"
      "    $display(\"%0d %0d %0d\", a, b, c);\n"
      "    '{a, b, c} = q; $display(\"%0d %0d %0d\", a, b, c);\n"
      "    '{A[2], A[0], A[1]} = A;\n"
      "    $display(\"%0d %0d %0d\", A[0], A[1], A[2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 3\n3 4 2\n7 8 9\n2 3 1\n");
}

// §10.9: an assignment pattern expression has a self-determined type, the
// value a variable of the type holds once initialized with it, wherever it is
// written. §10.9.2 places each member of a structure at its own offset and
// width, so `st'{3,4}` over two bytes is 16'h0304 as a system task argument
// and as an item of a queue concatenation, as it is assigned to an `st`.
// Concatenated at the items' 32 bits and cut to sixteen, it was 16'h0004.
TEST(AssignmentPatternSim, TypedStructurePatternIsPackedWhereverWritten) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct packed {byte a; byte b;} st;\n"
      "  st s; st sq[$];\n"
      "  initial begin\n"
      "    s = st'{3,4};\n"
      "    $display(\"%h %h\", s, st'{3,4});\n"
      "    sq = {st'{1,2}, st'{3,4}};\n"
      "    $display(\"%0d %h %h\", sq.size(), sq[0], sq[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0304 0304\n2 0102 0304\n");
}

}  // namespace
