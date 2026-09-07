#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LvalueSim, VarLvalueCompoundAdd) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  initial begin x = 10; x += 5; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(CompoundAssignOpEval, LtLtLtEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 1);

  auto* expr = MakeBinary(f.arena, TokenKind::kLtLtLtEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 16u);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(CompoundAssignOpEval, GtGtGtEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 256);

  auto* expr = MakeBinary(f.arena, TokenKind::kGtGtGtEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 16u);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(LvalueSim, CompoundAssignWithIndexedLhs) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int arr [0:3];\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 10; arr[3] = 0;\n"
      "    arr[2] += 5;\n"
      "  end\n"
      "endmodule\n",
      f, "arr[2]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(LvalueSim, CompoundAssignEvaluatesLvalueIndexOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 10; arr[3] = 0;\n"
      "    idx_calls = 0;\n"
      "    arr[idx_fn()] += 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* arr = f.ctx.FindVariable("arr");
  auto* calls = f.ctx.FindVariable("idx_calls");
  ASSERT_NE(arr, nullptr);
  ASSERT_NE(calls, nullptr);
  auto* arr_elem = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(arr_elem, nullptr);
  EXPECT_EQ(arr_elem->value.ToUint64(), 15u);
  EXPECT_EQ(calls->value.ToUint64(), 1u);
}

// §11.4.1: the once-only left-hand index rule applies to a packed bit-select
// lhs too, not just an unpacked array element. `data[idx_fn()] += ...` reads
// and writes the same bit of a single packed variable, and each of those steps
// re-derives the bit from the index expression; the side-effecting index must
// still be evaluated exactly once.
TEST(LvalueSim, CompoundAssignBitSelectIndexEvaluatedOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 3;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    data = 8'b0000_0000;\n"
      "    idx_calls = 0;\n"
      "    data[idx_fn()] += 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* data = f.ctx.FindVariable("data");
  auto* calls = f.ctx.FindVariable("idx_calls");
  ASSERT_NE(data, nullptr);
  ASSERT_NE(calls, nullptr);
  EXPECT_EQ(data->value.ToUint64(), 0x08u);
  EXPECT_EQ(calls->value.ToUint64(), 1u);
}

// §11.4.1: the once-only rule also governs an indexed part-select lhs
// (`data[f() +: w] += ...`). That lhs resolves through a different production
// path (packed part-select read + write) than a plain bit-select, and the base
// index is re-derived by both the read and the write, so a side-effecting base
// index must be evaluated exactly once here as well.
TEST(LvalueSim, CompoundAssignPartSelectBaseIndexEvaluatedOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    data = 8'b0000_0000;\n"
      "    idx_calls = 0;\n"
      "    data[idx_fn() +: 2] += 2'b11;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* data = f.ctx.FindVariable("data");
  auto* calls = f.ctx.FindVariable("idx_calls");
  ASSERT_NE(data, nullptr);
  ASSERT_NE(calls, nullptr);
  EXPECT_EQ(data->value.ToUint64(), 0x0Cu);
  EXPECT_EQ(calls->value.ToUint64(), 1u);
}

// §11.4.1: the blocking-assignment equivalence also holds when the lhs is a
// struct member (`s.field op= rhs`). That lhs kind takes its own production
// branch (member-access read + struct-field write) distinct from a plain
// variable or a select, so exercise `s.lo += 3` end-to-end from a real packed
// struct declaration and confirm only the addressed field is updated.
TEST(LvalueSim, CompoundAssignStructMemberLhs) {
  SimFixture f;
  auto* s = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [3:0] hi;\n"
      "    logic [3:0] lo;\n"
      "  } pair_t;\n"
      "  pair_t s;\n"
      "  initial begin\n"
      "    s.hi = 4'd2;\n"
      "    s.lo = 4'd5;\n"
      "    s.lo += 4'd3;\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(s, nullptr);
  // hi keeps 2 in the high nibble; lo becomes 5 + 3 = 8 in the low nibble.
  EXPECT_EQ(s->value.ToUint64(), 0x28u);
}

TEST(LvalueSim, CompoundAssignSelfReferenceDoublesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int a;\n"
      "  initial begin\n"
      "    a = 5;\n"
      "    a += a;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(LvalueSim, CompoundAssignArithBitwiseShiftThroughPipeline) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int sub, mul, divr, mod;\n"
      "  int band, bor, bxor;\n"
      "  int shl, shr;\n"
      "  initial begin\n"
      "    sub = 10;  sub  -= 3;\n"
      "    mul = 6;   mul  *= 2;\n"
      "    divr = 8;  divr /= 2;\n"
      "    mod = 17;  mod  %= 5;\n"
      "    band = 'hFF; band &= 'h0F;\n"
      "    bor  = 'h01; bor  |= 'h10;\n"
      "    bxor = 'hAA; bxor ^= 'hFF;\n"
      "    shl = 1;   shl  <<= 4;\n"
      "    shr = 256; shr  >>= 4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("sub")->value.ToUint64(), 7u);
  EXPECT_EQ(f.ctx.FindVariable("mul")->value.ToUint64(), 12u);
  EXPECT_EQ(f.ctx.FindVariable("divr")->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("mod")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("band")->value.ToUint64(), 0x0Fu);
  EXPECT_EQ(f.ctx.FindVariable("bor")->value.ToUint64(), 0x11u);
  EXPECT_EQ(f.ctx.FindVariable("bxor")->value.ToUint64(), 0x55u);
  EXPECT_EQ(f.ctx.FindVariable("shl")->value.ToUint64(), 16u);
  EXPECT_EQ(f.ctx.FindVariable("shr")->value.ToUint64(), 16u);
}

// §11.4.1 gives each element of a concatenation lvalue the bits its own width
// claims, and §11.5.1 gives a select the bits its indices name. The element
// walk read the width of the resolved variable instead, so a select element was
// sized at the whole of its variable and written whole: `{a[3:0], b}` took all
// of `a` and drew the boundary between the two elements in the wrong place, so
// `b` took the wrong bits as well.
//
// `a` is set to 8'hFF first, so a write of the whole variable is told from a
// write of the low nibble by what the high nibble holds afterwards.
TEST(LvalueSim, ConcatSelectElementTakesOnlyTheBitsItNames) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    {a[3:0], b} = 12'h123;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFFu, 0xF1u);
}

// The element to the right of the select, which a mis-sized first element moves
// the boundary of. With the select claiming four bits, `b` takes the low eight
// of 12'h123.
TEST(LvalueSim, ConcatElementAfterASelectTakesTheBitsBelowIt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    {a[3:0], b} = 12'h123;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFFu, 0x23u);
}

// Nothing in §11.4.1 drops the x and z bits of what is assigned. The slice was
// taken through Logic4Vec::ToUint64, which returns `aval & ~bval`, so both
// arrived as 0.
TEST(LvalueSim, ConcatLvalueCarriesUnknownBitsToItsElements) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial {a, b} = 16'bzzzzxxxx10101010;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "zzzzxxxx");
}

// And nothing bounds a concatenation at one word. ToUint64 reads words[0]
// alone, so the element above bit 63 took nothing.
TEST(LvalueSim, ConcatLvalueReachesElementsAboveTheFirstWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [63:0] hi;\n"
      "  logic [63:0] lo;\n"
      "  initial {hi, lo} = 128'h1234_0000_0000_0000_0000_0000_0000_0000;\n"
      "endmodule\n",
      f, "hi");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x1234000000000000ull);
}

// §11.4.1 makes `a op= b` "semantically equivalent to a blocking assignment",
// writing `a[i]+=2;` as the same statement as `a[i] = a[i] +2;`. So §10.7
// truncates the result into the target as it would any other assignment, and
// §6.11.2 converts the unknowns a 2-state target has no room for. The result
// was written over the target instead, so the target took the operation's
// width.

// The eight bits the addition is evaluated at do not fit the four the target
// declares. 17 is what the target read when it took the operation's width; 1 is
// what four bits hold of it. The width is read as well as the value, because a
// target that grew is the defect itself rather than a consequence of it.
TEST(LvalueSim, CompoundAssignTruncatesToTheTargetWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'h2;\n"
      "    v += 8'h0F;\n"
      "  end\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 4u);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §6.11.2 gives a `bit` no unknown to hold, and the blocking assignment §11.4.1
// makes this equivalent to converts them. The value is read through IsKnown as
// well as by number, since an x reads as zero either way.
TEST(LvalueSim, CompoundAssignZeroesXzIntoATwoStateTarget) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] u;\n"
      "  bit [7:0] b;\n"
      "  initial begin\n"
      "    u = 8'b1010_x10z;\n"
      "    b = 8'h00;\n"
      "    b |= u;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

// §11.3.6: an assignment expression "casts the right-hand side to the left-hand
// data type, stacks it, updates the left-hand side, and returns the stacked
// value", and "the data type of the value that is returned is the data type of
// the left-hand side". So what `b = (a += 1)` reads is what `a` holds, not what
// the addition produced: `b = (a+=1)` is the clause's own example. Sixteen is
// the untruncated sum, and zero is the four bits `a` keeps of it.
TEST(LvalueSim, CompoundAssignExpressionYieldsTheTargetsDataType) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  int b;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    b = (a += 1);\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §11.4.1's once-only rule is a property of the operator, not of where it is
// written, and the three cases above all write it as a bare statement -- which
// is intercepted before the expression evaluator and reaches the path that
// snapshots the indices. §11.3.6 admits the parenthesized form, and any
// compound assignment used as an operand reaches EvalCompoundAssign instead,
// where the allocation, the read and the write each re-derived the target from
// the index and called it again.

// The unpacked array element, written as an expression. The counter is what
// discriminates: the value was already right, each call returning the same
// index.
TEST(LvalueSim, CompoundAssignAsAnExpressionEvaluatesLvalueIndexOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int idx_calls;\n"
      "  int q;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 10; arr[3] = 0;\n"
      "    idx_calls = 0;\n"
      "    q = (arr[idx_fn()] += 5);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* arr_elem = f.ctx.FindVariable("arr[2]");
  auto* calls = f.ctx.FindVariable("idx_calls");
  ASSERT_NE(arr_elem, nullptr);
  ASSERT_NE(calls, nullptr);

  EXPECT_EQ(arr_elem->value.ToUint64(), 15u);
  EXPECT_EQ(calls->value.ToUint64(), 1u);
}

// The packed bit-select, written as an expression. It reaches a different
// writer from the array element above, so the count is a separate reading.
TEST(LvalueSim, CompoundAssignAsAnExpressionEvaluatesBitSelectIndexOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  int idx_calls;\n"
      "  logic q;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 3;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    data = 8'b0000_0000;\n"
      "    idx_calls = 0;\n"
      "    q = (data[idx_fn()] += 1'b1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* data = f.ctx.FindVariable("data");
  auto* calls = f.ctx.FindVariable("idx_calls");
  ASSERT_NE(data, nullptr);
  ASSERT_NE(calls, nullptr);

  EXPECT_EQ(data->value.ToUint64(), 0x08u);
  EXPECT_EQ(calls->value.ToUint64(), 1u);
}

}  // namespace
