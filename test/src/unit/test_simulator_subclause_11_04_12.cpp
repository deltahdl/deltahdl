#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §11.4.12: bits of a concatenation may be selected as if it were a packed
// array with range [n-1:0]. Driven end-to-end from real source so the select
// operates on a concatenation produced by the parser and elaborator, not a
// hand-built expression. {a,b} with a=4'hA, b=4'h5 is 8'hA5 = 1010_0101, so
// [5:2] extracts 4'h9 and bit [7] (the MSB) is 1.
TEST(ConcatenationSim, PartSelectOnConcatRhsFullPipeline) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [3:0] a, b;\n"
                      "  logic [3:0] result;\n"
                      "  initial begin\n"
                      "    a = 4'hA;\n"
                      "    b = 4'h5;\n"
                      "    result = {a, b}[5:2];\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0x9u);
}

// A single bit of a concatenation is indexed through the same [n-1:0] packed
// range. {a,b} = 8'hA5 = 1010_0101, so bit [7] (MSB) is 1, bit [0] (LSB) is 1,
// and bit [4] is 0. Driven end-to-end from real source.
TEST(ConcatenationSim, BitSelectOnConcatRhsFullPipeline) {
  const char* src =
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic b7, b0, b4;\n"
      "  initial begin\n"
      "    a = 4'hA;\n"
      "    b = 4'h5;\n"
      "    b7 = {a, b}[7];\n"
      "    b0 = {a, b}[0];\n"
      "    b4 = {a, b}[4];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "b7"), 1u);
  EXPECT_EQ(RunAndGet(src, "b0"), 1u);
  EXPECT_EQ(RunAndGet(src, "b4"), 0u);
}

// §11.4.12: a concatenation is a packed vector usable on the left-hand side of
// an assignment. The LRM's own example uses scalar (1-bit) targets. Assigning
// 3'b101 to {log1, log2, log3} distributes bits MSB-first, so log1=1, log2=0,
// log3=1; reading them back through the same concatenation reconstructs 3'b101.
TEST(ConcatenationSim, LhsConcatDistributesToScalarTargets) {
  const char* src =
      "module t;\n"
      "  logic log1, log2, log3;\n"
      "  logic [2:0] r;\n"
      "  initial begin\n"
      "    {log1, log2, log3} = 3'b101;\n"
      "    r = {log1, log2, log3};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "r"), 0b101u);
  EXPECT_EQ(RunAndGet(src, "log1"), 1u);
  EXPECT_EQ(RunAndGet(src, "log2"), 0u);
  EXPECT_EQ(RunAndGet(src, "log3"), 1u);
}

TEST(EvalOp, ConcatXZPropagation) {
  SimFixture f;

  MakeVar4(f, "ca", 4, 0b1001, 0b0101);

  auto* bv = f.ctx.CreateVariable("cb", 4);
  bv->value = MakeLogic4VecVal(f.arena, 4, 0b0101);

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "ca"));
  concat->elements.push_back(MakeId(f.arena, "cb"));

  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);

  EXPECT_EQ(result.words[0].aval, 0x95u);
  EXPECT_EQ(result.words[0].bval, 0x50u);
}

TEST(EvalOp, ConcatWidthIsSumOfElements) {
  SimFixture f;

  auto* va = f.ctx.CreateVariable("a", 8);
  va->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* vb = f.ctx.CreateVariable("b", 4);
  vb->value = MakeLogic4VecVal(f.arena, 4, 0xC);

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "a"));
  concat->elements.push_back(MakeId(f.arena, "b"));

  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.width, 12u);
  EXPECT_EQ(result.ToUint64(), 0xABCu);
}

// §10.4 puts procedural assignments "within procedures such as always, initial,
// task, and function", so §11.4.12's left-hand concatenation is the same
// statement inside a subroutine body as in the initial block above. The
// subroutine body runs on the statement executor in eval_function_body.cpp,
// which named no concatenation form at all, so the assignment wrote nothing and
// reported nothing and every target kept the value it already had. The cases
// below write from a subroutine and read from outside it.

// The LRM's own example, moved into a function body. Each target is read
// separately, since a distribution that put the whole value in one of them
// would still leave the others at 0 and so would be told apart by reading all
// three rather than their concatenation.
TEST(ConcatenationSim, LhsConcatInAFunctionBodyDistributesToScalarTargets) {
  const char* src =
      "module t;\n"
      "  logic log1, log2, log3;\n"
      "  function void put();\n"
      "    {log1, log2, log3} = 3'b101;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    log1 = 0; log2 = 0; log3 = 0;\n"
      "    put();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "log1"), 1u);
  EXPECT_EQ(RunAndGet(src, "log2"), 0u);
  EXPECT_EQ(RunAndGet(src, "log3"), 1u);
}

// A task body takes the same executor by its own call path, so neither case
// stands for the other. §11.6 sizes the sum by the concatenation's width, which
// is where the carry-out lands, so this reads the width and the write together:
// carry is the bit a sixteen-bit sum could not hold.
TEST(ConcatenationSim, LhsConcatInATaskBodyTakesTheCarryOut) {
  const char* src =
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  logic carry;\n"
      "  logic [15:0] acc;\n"
      "  task add();\n"
      "    {carry, acc} = a + b;\n"
      "  endtask\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    carry = 0; acc = 16'hFFFF;\n"
      "    add();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "carry"), 1u);
  EXPECT_EQ(RunAndGet(src, "acc"), 0u);
}

// §11.4.12's concatenation may contain a concatenation, and the inner one takes
// its slice and distributes it again. A writer that walked the elements flatly
// would hand the inner brace's whole slice to one target or drop it, so b and c
// are what separate the readings.
TEST(ConcatenationSim, LhsConcatInAFunctionBodyReachesANestedConcatenation) {
  const char* src =
      "module t;\n"
      "  logic p, q, r;\n"
      "  function void put();\n"
      "    {p, {q, r}} = 3'b101;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    p = 0; q = 0; r = 0;\n"
      "    put();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "p"), 1u);
  EXPECT_EQ(RunAndGet(src, "q"), 0u);
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// An element that is a select takes the bits it named and leaves the rest of
// its variable standing. `v` is loaded with 8'hF0 first, so a writer that gave
// the element's slice to the whole variable would read 0x0A where the part
// written alone reads 0xFA.
TEST(ConcatenationSim, LhsConcatInAFunctionBodyWritesOnlyTheBitsASelectNames) {
  const char* src =
      "module t;\n"
      "  logic x;\n"
      "  logic [7:0] v;\n"
      "  function void put();\n"
      "    {x, v[3:0]} = 5'b1_1010;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    v = 8'hF0;\n"
      "    put();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "x"), 1u);
  EXPECT_EQ(RunAndGet(src, "v"), 0xFAu);
}

}  // namespace
