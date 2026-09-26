
#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/compiled_sim.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(BlockingAssignSim, BlockingOverwriteInOrder) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd100;\n"
      "    x = 8'd200;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 200u);
}

TEST(BlockingAssignCompiledSim, ExecuteBlockingAssign) {
  CompiledSimFixture f;
  auto* x_var = f.ctx.CreateVariable("x", 32);
  x_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kIdentifier;
  lhs->text = "x";
  auto* rhs = f.arena.Create<Expr>();
  rhs->kind = ExprKind::kIntegerLiteral;
  rhs->int_val = 42;
  auto* assign = f.arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;
  assign->lhs = lhs;
  assign->rhs = rhs;

  auto* block = f.arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(assign);

  auto compiled = ProcessCompiler::Compile(1, block);
  EXPECT_TRUE(compiled.IsValid());
  compiled.Execute(f.ctx);
  EXPECT_EQ(x_var->value.ToUint64(), 42u);
}

TEST(BlockingAssignSim, EightBitAssignPreservesWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] val;\n"
      "  initial begin\n"
      "    val = 8'hAB;\n"
      "  end\n"
      "endmodule\n",
      f, "val");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(BlockingAssignSim, ParallelBlockDoesNotPreventExecution) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a, b, c;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin a = 1; b = a + 1; end\n"
      "      c = 99;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 2u}, {"c", 99u}});
}

TEST(BlockingAssignSim, SelfAssignmentPreservesValue) {
  auto result = RunAndGet(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = 42;\n"
      "    x = x;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 42u);
}

TEST(BlockingAssignSim, IntraAssignmentDelayEvaluatesLvalueAfterDelay) {
  SimFixture f;
  auto* arr1 = RunAndFindVar(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int idx;\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 0; arr[3] = 0;\n"
      "    idx = 1;\n"
      "    arr[idx] = #5 99;\n"
      "  end\n"
      "  initial begin\n"
      "    #2 idx = 3;\n"
      "  end\n"
      "endmodule\n",
      f, "arr[1]");
  ASSERT_NE(arr1, nullptr);
  auto* arr3 = f.ctx.FindVariable("arr[3]");
  ASSERT_NE(arr3, nullptr);
  EXPECT_EQ(arr1->value.ToUint64(), 0u);
  EXPECT_EQ(arr3->value.ToUint64(), 99u);
}

// The intra-assignment delay of a blocking assignment (§10.4.1) is a §9.4.1
// delay control, so a negative delay must be reinterpreted as a
// two's-complement unsigned integer the width of a time variable, exactly as a
// standalone delay does. A 32-bit -1 delay therefore advances time by the full
// 64-bit all-ones value, not by the raw zero-extended 0xFFFFFFFF. This
// discriminates against taking the delay's raw bits.
TEST(BlockingAssignSim,
     NegativeIntraAssignmentDelayReinterpretedAsTimeVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int d;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    d = -1;\n"
      "    x = #d 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
  EXPECT_EQ(f.ctx.CurrentTime().ticks, ~uint64_t{0});
}

// An intra-assignment delay whose value has any unknown bits (§9.4.1) must be
// treated as a zero delay, even when the known bits are nonzero. Here the delay
// 4'b10xx has known high bits worth 8, but the unknown low bits force a zero
// delay, so the assignment completes at time 0. This discriminates against a
// raw-bits reading that would advance time by 8.
TEST(BlockingAssignSim, MultibitUnknownIntraAssignmentDelayTreatedAsZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd1;\n"
      "    x = #(4'b10xx) 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.CurrentTime().ticks, 0u);
}

// §10.4.1 permits a variable of any of the assignment-compatible LHS forms; a
// struct member select (§7.2) is one such form and reaches production through
// the kMemberAccess lvalue-resolution path (ResolveLhsVariable/BuildLhsName),
// distinct from the plain-identifier and select forms already exercised. Each
// member write lands at its own field offset within the packed struct, so
// writing both members from scratch and reading back the whole struct verifies
// the full pipeline resolves and composes member-LHS blocking assignments. The
// existing §7.2.1 coverage overwrites a single member of a pre-initialized
// struct; this drives two distinct member LHS targets and observes the result.
TEST(BlockingAssignSim, StructMemberLhsWritesComposeFullStruct) {
  auto result = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t s;\n"
      "  initial begin\n"
      "    s.hi = 8'hAB;\n"
      "    s.lo = 8'hCD;\n"
      "  end\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(result, 0xABCDu);
}

// §6.8: "A variable is an abstraction of a data storage element. A variable
// shall store a value from one assignment to the next." Two declarations are
// two storage elements, so a statement that only reads one of them cannot
// change what it stores. A §10.4.1 assignment therefore has to leave its
// target holding a copy of the right-hand value; a target that instead shares
// the source's storage is one storage element under two names, and the value
// the source stores no longer runs from one assignment to the next.
//
// A 2-state target makes the sharing observable within the one statement.
// §6.11.2 gives `bit` no unknown values, so the assignment coerces the stored
// value's x bits away, and shared storage performs that coercion on the
// source's own bits: `x` is not a target of the second statement, only its
// operand, yet its unknowns would be gone once the statement finishes.
//
// Both variables are eight bits deliberately. Unequal widths would make the
// assignment resize, which builds the value in a fresh store and hides the
// sharing; the matching widths are what let the read value reach the target
// unresized.
//
// The assertions read words[0].aval and words[0].bval because ToUint64 cannot
// see this: it projects aval & ~bval, so an x bit already reads 0 and clearing
// it changes nothing ToUint64 reports -- `x` reads 0xA0 through ToUint64
// whether its unknowns survived or not. The stored bits of 8'b1010xxxx are
// aval 0xAF and bval 0x0F, an x bit being aval 1 with bval 1; coercing that to
// 2-state gives aval 0xA0 and bval 0x00, which is what `y` alone must hold.
TEST(BlockingAssignSim, TwoStateTargetCoercionLeavesSourceUnknownBitsIntact) {
  SimFixture f;
  auto* src_var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  bit [7:0] y;\n"
      "  initial begin\n"
      "    x = 8'b1010xxxx;\n"
      "    y = x;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(src_var, nullptr);
  auto* dst_var = f.ctx.FindVariable("y");
  ASSERT_NE(dst_var, nullptr);
  EXPECT_EQ(src_var->value.words[0].aval & 0xFFu, 0xAFu);
  EXPECT_EQ(src_var->value.words[0].bval & 0xFFu, 0x0Fu);
  EXPECT_EQ(dst_var->value.words[0].aval & 0xFFu, 0xA0u);
  EXPECT_EQ(dst_var->value.words[0].bval & 0xFFu, 0x00u);
}

// The same §6.8 storage-element independence, observed through a write that
// lands after the assignment rather than inside it. A packed struct member
// assignment (§7.2) deposits into a window of the whole struct's storage in
// place, writing through the words the struct already holds; so a target left
// naming its source's storage is written by every later member assignment to
// the target, and the source records writes it never received.
//
// A packed struct lays its first member at the high bits, so `s.a = 8'hA5;
// s.b = 8'h3C;` stores 16'hA53C, member `a` occupying bits [15:8] and `b` bits
// [7:0]. `d = s` must give `d` its own 16'hA53C. Depositing 8'h00 over `d.b`
// clears bits [7:0] of `d` alone, leaving `d` at 16'hA500 and `s` still at
// 16'hA53C; shared storage reports 16'hA500 for both, `s` having lost the
// 8'h3C it was assigned and never overwrote.
//
// Every bit involved is known, so ToUint64 reports the stored value exactly
// and its aval & ~bval projection hides nothing. Both structs are sixteen bits
// wide, which is again what keeps the assignment from resizing.
TEST(BlockingAssignSim, PackedMemberDepositOnCopyLeavesSourceIntact) {
  SimFixture f;
  auto* whole = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } p_t;\n"
      "  p_t s;\n"
      "  p_t d;\n"
      "  initial begin\n"
      "    s.a = 8'hA5;\n"
      "    s.b = 8'h3C;\n"
      "    d = s;\n"
      "    d.b = 8'h00;\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(whole, nullptr);
  auto* copy = f.ctx.FindVariable("d");
  ASSERT_NE(copy, nullptr);
  EXPECT_EQ(whole->value.ToUint64(), 0xA53Cu);
  EXPECT_EQ(copy->value.ToUint64(), 0xA500u);
}

// §6.8 draws no distinction between the writers that reach a variable, so the
// independence the two cases above claim of a member deposit is claimed here
// of a bit-select write (§11.5.1) as well. The select write rebuilds: it
// extracts the whole variable into a fresh store, deposits into that, and
// replaces the variable's value with it, rather than writing through the words
// the variable already holds. So this case states the boundary of the rule
// rather than one more way to break it -- what it discriminates against is a
// select write rewritten to deposit in place, which the in-place deposit used
// by the member path invites, and which would then carry every bit-select
// write on a copy back into whatever the copy was made from.
//
// p = 8'hA5 is 1010_0101, so clearing q[0] leaves q at 8'hA4 and p at 8'hA5 --
// p's low bit being the 1 that q's write cleared, so a write that reached p
// would be read off the value rather than inferred. The widths match here for
// the same reason they match above: an assignment that resized would not be
// the assignment whose target this case is about.
TEST(BlockingAssignSim, BitSelectWriteOnCopyLeavesSourceIntact) {
  SimFixture f;
  auto* original = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] p;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    p = 8'hA5;\n"
      "    q = p;\n"
      "    q[0] = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(original, nullptr);
  auto* selected = f.ctx.FindVariable("q");
  ASSERT_NE(selected, nullptr);
  EXPECT_EQ(original->value.ToUint64(), 0xA5u);
  EXPECT_EQ(selected->value.ToUint64(), 0xA4u);
}

// §10.4.1 (printed page 252): the index expression a variable_lvalue carries
// is evaluated at the one time the clause names, and §11.4.2 (printed page 275)
// makes `j++` an assignment of its own, so the statement increments j once and
// writes the element the first value of j names. The element writers are asked
// in turn, and the first of them evaluated the index to spell a fixed-size
// array's element, found no such element for a dynamic array, and declined, the
// queue writer that answers a dynamic array then evaluating it again: j ended
// at 2 and 7 landed at index 1.
TEST(BlockingAssignSim, DynamicArrayElementIndexEvaluatedOnce) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int d[];\n"
      "  int j;\n"
      "  initial begin\n"
      "    d = new[4];\n"
      "    d[j++] = 7;\n"
      "    $display(\"%0d %0d %0d\", j, d[0], d[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 7 0\n");
}

// §10.4.1 as above, for §7.10's queue, whose element writer is reached by the
// same decline.
TEST(BlockingAssignSim, QueueElementIndexEvaluatedOnce) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int q[$];\n"
      "  int k;\n"
      "  initial begin\n"
      "    q = '{0, 0, 0, 0};\n"
      "    q[k++] = 7;\n"
      "    $display(\"%0d %0d %0d\", k, q[0], q[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 7 0\n");
}

// §10.4.1 as above, for §7.8's associative array: the one write allocates the
// one entry at the key the first value of m names, where the second
// evaluation allocated key 1.
TEST(BlockingAssignSim, AssocElementIndexEvaluatedOnce) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int aa[int];\n"
      "  int m;\n"
      "  initial begin\n"
      "    aa[m++] = 7;\n"
      "    $display(\"%0d %0d %0d %0d\", m, aa.num(), aa.exists(0), aa[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1 7\n");
}

// §10.4.1 as above, for §11.5.1's bit-select of a packed variable: the
// element writers each decline a name that is no array, the first having
// evaluated the index already, and the bit-select writer evaluated it again,
// so i ended at 2 and bit 1 was set rather than bit 0.
TEST(BlockingAssignSim, PackedBitSelectIndexEvaluatedOnce) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  int i;\n"
      "  initial begin\n"
      "    v = 8'h00;\n"
      "    v[i++] = 1'b1;\n"
      "    $display(\"%0d %b\", i, v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 00000001\n");
}

// §10.4.1 as above, in the shape UVM's uvm_phase::get_adjacent_successor_nodes
// fills its output array with: a dynamic array passed by reference (§13.5.2),
// sized in the function and written once per element through `idx++` in a
// foreach. Each write landed one element further along, the last past the
// end, so the array came back '{0, 10, 0, 11} and one size larger.
TEST(BlockingAssignSim, RefDynamicArrayFilledThroughPostIncrementIndex) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  function automatic void fill(ref int succ[]);\n"
      "    int idx;\n"
      "    succ = new[3];\n"
      "    foreach (succ[i]) succ[idx++] = i + 10;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    int d[];\n"
      "    fill(d);\n"
      "    $display(\"%0d %0d %0d %0d\", d.size(), d[0], d[1], d[2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 10 11 12\n");
}

// §10.4.1 as above, for a queue element written as one element of a
// concatenation target (§11.4.12): the concatenation's element writer asks
// the same writers in the same order, and evaluated the index twice the same
// way.
TEST(BlockingAssignSim, ConcatQueueElementIndexEvaluatedOnce) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  byte q[$];\n"
      "  byte b;\n"
      "  int k;\n"
      "  initial begin\n"
      "    q = '{0, 0};\n"
      "    {q[k++], b} = 16'h0703;\n"
      "    $display(\"%0d %0d %0d %0d\", k, q[0], q[1], b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 7 0 3\n");
}

// §10.4.1 as above, with an intra-assignment delay (§9.4.5): the index is
// evaluated once, when the delay has elapsed, by the store the delayed form
// makes after its wait.
TEST(BlockingAssignSim, DelayedDynamicArrayElementIndexEvaluatedOnce) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int d[];\n"
      "  int j;\n"
      "  initial begin\n"
      "    d = new[4];\n"
      "    d[j++] = #1 7;\n"
      "    $display(\"%0d %0d %0d\", j, d[0], d[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 7 0\n");
}

}  // namespace
