#include <string>

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

// §11.4.1's once-only left-hand index rule is read the same way each time an
// lhs form is claimed for it: an automatic function bumps a counter and returns
// a fixed index, so the value the target ends at is the same however many times
// the index ran, and the count is what discriminates. This runs one such design
// and reads both.
void RunAndCheckIndexOnce(const std::string& src, const char* target,
                          uint64_t expected) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable(target);
  auto* calls = f.ctx.FindVariable("idx_calls");
  ASSERT_NE(var, nullptr);
  ASSERT_NE(calls, nullptr);
  EXPECT_EQ(var->value.ToUint64(), expected);
  EXPECT_EQ(calls->value.ToUint64(), 1u);
}

TEST(LvalueSim, CompoundAssignEvaluatesLvalueIndexOnce) {
  RunAndCheckIndexOnce(
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
      "arr[2]", 15u);
}

// §11.4.1: the once-only left-hand index rule applies to a packed bit-select
// lhs too, not just an unpacked array element. `data[idx_fn()] += ...` reads
// and writes the same bit of a single packed variable, and each of those steps
// re-derives the bit from the index expression; the side-effecting index must
// still be evaluated exactly once.
TEST(LvalueSim, CompoundAssignBitSelectIndexEvaluatedOnce) {
  RunAndCheckIndexOnce(
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
      "data", 0x08u);
}

// §11.4.1: the once-only rule also governs an indexed part-select lhs
// (`data[f() +: w] += ...`). That lhs resolves through a different production
// path (packed part-select read + write) than a plain bit-select, and the base
// index is re-derived by both the read and the write, so a side-effecting base
// index must be evaluated exactly once here as well.
TEST(LvalueSim, CompoundAssignPartSelectBaseIndexEvaluatedOnce) {
  RunAndCheckIndexOnce(
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
      "data", 0x0Cu);
}

// §11.4.1's once-only rule is a property of the operator, not of where it is
// written, and the three cases above all write it as a bare statement -- which
// is intercepted before the expression evaluator and reaches the path that
// snapshots the indices. §11.3.6 admits the parenthesized form, and any
// compound assignment used as an operand reaches EvalCompoundAssign instead,
// where the allocation, the read and the write each re-derived the target from
// the index and called it again.
TEST(LvalueSim, CompoundAssignAsAnExpressionEvaluatesLvalueIndexOnce) {
  RunAndCheckIndexOnce(
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
      "arr[2]", 15u);
}

// The packed bit-select written as an expression, which reaches a different
// writer from the array element above and so is a separate reading.
TEST(LvalueSim, CompoundAssignAsAnExpressionEvaluatesBitSelectIndexOnce) {
  RunAndCheckIndexOnce(
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
      "data", 0x08u);
}

// §11.4.1 makes `a op= b` "semantically equivalent to a blocking assignment",
// and a blocking assignment writes its target once. A subroutine body runs on
// the statement executor in eval_function_body.cpp rather than the one in
// statement_assign_core.cpp, and that executor evaluated the statement's
// right-hand side -- which the parser builds as the compound operator over the
// statement's own left-hand side, so evaluating it had already written the
// target -- and then wrote the value it handed back to that same left-hand side
// a second time. A fixed index hides the second write, because it lands the
// same value on the same element; an index function that returns a fresh index
// on every call does not. The first write puts 5 in arr[1] and there is no
// second write, so arr[2] stays 0 and idx_fn has run once. Before the fix
// arr[1] and arr[2] both held 5 and idx_fn had run twice.
TEST(LvalueSim, CompoundAssignInAFunctionBodyWritesTheTargetOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return idx_calls;\n"
      "  endfunction\n"
      "  function void bump();\n"
      "    arr[idx_fn()] += 5;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 0; arr[3] = 0;\n"
      "    idx_calls = 0;\n"
      "    bump();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* written = f.ctx.FindVariable("arr[1]");
  auto* untouched = f.ctx.FindVariable("arr[2]");
  auto* calls = f.ctx.FindVariable("idx_calls");
  ASSERT_NE(written, nullptr);
  ASSERT_NE(untouched, nullptr);
  ASSERT_NE(calls, nullptr);
  EXPECT_EQ(written->value.ToUint64(), 5u);
  EXPECT_EQ(untouched->value.ToUint64(), 0u);
  EXPECT_EQ(calls->value.ToUint64(), 1u);
}

// §11.4.1's once-only left-hand index rule read through the subroutine
// executor. The index is fixed here, so the target ends at 15 however many
// times the statement wrote it and the call count is the whole reading. Before
// the fix the second write re-derived the element from the index expression and
// idx_fn ran twice.
TEST(LvalueSim, CompoundAssignInAFunctionBodyEvaluatesLvalueIndexOnce) {
  RunAndCheckIndexOnce(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 2;\n"
      "  endfunction\n"
      "  function void bump();\n"
      "    arr[idx_fn()] += 5;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 10; arr[3] = 0;\n"
      "    idx_calls = 0;\n"
      "    bump();\n"
      "  end\n"
      "endmodule\n",
      "arr[2]", 15u);
}

// A task called with parentheses runs its body on the ordinary statement
// executor rather than the subroutine one: SetupTaskCall claims a kTaskDecl and
// ExecInlineTaskCall walks the body through ExecStmt, where a void function of
// the same shape is declined there and reaches ExecFunctionBody. So a task body
// never carried the second write and this reading passed before the fix. It is
// §11.4.1's rule read through a task call rather than a second reading of the
// subroutine executor, and the function case above is what claims that.
TEST(LvalueSim, CompoundAssignInATaskBodyEvaluatesLvalueIndexOnce) {
  RunAndCheckIndexOnce(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 2;\n"
      "  endfunction\n"
      "  task bump();\n"
      "    arr[idx_fn()] += 5;\n"
      "  endtask\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 10; arr[3] = 0;\n"
      "    idx_calls = 0;\n"
      "    bump();\n"
      "  end\n"
      "endmodule\n",
      "arr[2]", 15u);
}

// The plain variable form of the same statement, which nothing read inside a
// subroutine body before. It does not discriminate on its own: both writes
// carried the same sum to the same variable, so `x` read 15 before the fix as
// well. This is coverage of the form in that position rather than a second
// claim about the doubled write.
TEST(LvalueSim, VarLvalueCompoundAddInAFunctionBody) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  function void bump();\n"
      "    x += 5;\n"
      "  endfunction\n"
      "  initial begin x = 10; bump(); end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
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

// §11.4.1 makes `i += 1.75` the blocking assignment `i = i + 1.75`, so
// §11.8.1 evaluates the sum in real arithmetic and §6.12.1 then converts the
// real to the integer target "by rounding to the nearest integer" with ties
// away from zero. 2.75 is away from the tie, so the answer is 3 and the two
// wrong answers it excludes are distinct from it and from each other:
// truncation reads 2, and a raw resize of the 64-bit IEEE-754 double into a
// 32-bit target reads 0, since the low word of 2.75's bit pattern
// (0x4006000000000000) is zero.
TEST(LvalueSim, CompoundAssignOfARealToAnIntegerTarget) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int i;\n"
      "  initial begin\n"
      "    i = 1;\n"
      "    i += 1.75;\n"
      "  end\n"
      "endmodule\n",
      f, "i");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// The same conversion in a subroutine body, which reaches it by a different
// route. The subroutine executor used to write the target twice, and the second
// write was the one that applied §6.12.1; routing the statement to the single
// read-modify-write the ordinary executor uses would have dropped the
// conversion, because the plain variable write does not apply it. So this is
// the reading that holds §6.12.1 in place across the change rather than one
// about the doubled write, and the wrong answer it excludes is 0 -- the low 32
// bits of 2.75 as a double.
TEST(LvalueSim, CompoundAssignOfARealToAnIntegerTargetInAFunctionBody) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int i;\n"
      "  function void bump();\n"
      "    i += 1.75;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    i = 1;\n"
      "    bump();\n"
      "  end\n"
      "endmodule\n",
      f, "i");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
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

// §11.4.1's `( operator_assignment )` primary is the one form of a compound
// assignment that does not arrive as a statement: the parser wraps a bare
// `x += 2;` as a blocking assign whose rhs carries the operator, and
// TryDispatchSpecialBlockingAssign hands that to ApplyCompoundAssignOp, which
// writes through WriteVar. Parenthesized, the same operator is an embedded
// assignment expression whose target is its own lhs, so the dispatcher declines
// it and EvalExpr routes it to EvalCompoundAssign -- which stores to the
// variable directly. §9.4.2 makes that store a change like any other, and an
// `always @(x)` parked on the target is entitled to see it.
//
// The delays keep one write to a time step so the tally is unambiguous, and the
// third write adds nothing: the awaiter compares against the value it captured
// when it armed, so a store of the value already held is not a change and does
// not wake anyone. That fixes three separate wrong answers on `hits` -- 0 when
// the embedded store notifies nobody, 1 when only the first change is seen, and
// 4 when every store notifies whether or not it changed anything. §11.3.6 gives
// the expression a value as well as an effect, so `y` pins what the last one
// yielded beside `x`, which pins what it stored.
TEST(LvalueSim, CompoundAssignExpressionWakesAnEventControlOnItsTarget) {
  SimFixture f;
  const std::string kSrc =
      "module t;\n"
      "  int x;\n"
      "  int y;\n"
      "  int hits;\n"
      "  always @(x) hits = hits + 1;\n"
      "  initial begin\n"
      "    #1 y = (x += 3);\n"
      "    #1 y = (x += 0);\n"
      "    #1 y = (x += 5);\n"
      "    #1 y = (x += 4);\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n";
  auto* hits = RunAndFindVar(kSrc, f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 12u);

  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 12u);
}

}  // namespace
