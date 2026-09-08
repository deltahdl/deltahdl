#include "helpers_reported_error.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(DynamicArrayNewSimulation, NewAllocatesWithSize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[4];\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

TEST(DynamicArrayNewSimulation, NewDefaultInitializesElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[3];\n"
      "    result = d[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayNewSimulation, NewZeroSizeCreatesEmpty) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[0];\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayNewSimulation, NewWithInitCopiesElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20, 30};\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[3](src);\n"
      "    result = d[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(DynamicArrayNewSimulation, NewWithInitTruncates) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20, 30, 40};\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[2](src);\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 2u);
}

TEST(DynamicArrayNewSimulation, NewWithInitTruncatesKeepsLeadingElements) {
  // §7.5.1: when the initialization array is larger than the size argument it
  // is truncated to the size argument, keeping the leading elements. Here
  // new[2] of {10,20,30,40} must yield {10,20}, so d[1] is the second source
  // element (20), not a trailing one.
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20, 30, 40};\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[2](src);\n"
      "    result = d[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(DynamicArrayNewSimulation, NewWithInitPads) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20};\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[5](src);\n"
      "    result = d[3];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayNewSimulation, NewWithInitPreservesOnPad) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20};\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[5](src);\n"
      "    result = d[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(DynamicArrayNewSimulation, SelfReferenceResize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{1, 2, 3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[6](d);\n"
      "    result = d[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(DynamicArrayNewSimulation, SelfReferenceResizeNewSize) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{1, 2, 3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[6](d);\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 6u);
}

TEST(DynamicArrayNewSimulation, NewNegativeSizeIsError) {
  // §7.5.1: it shall be an error if the value of the size operand is negative.
  // The report stands on the size operand itself, so it names line 6 where `n`
  // is written inside new[], not line 5 where n took its negative value.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[];\n"
      "  int n;\n"
      "  initial begin\n"
      "    n = -1;\n"
      "    d = new[n];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "dynamic array new[] size is negative", 6,
                            "7.5.1"));
}

TEST(DynamicArrayNewSimulation, SelfReferenceResizePadZero) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{1, 2, 3};\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[6](d);\n"
      "    result = d[4];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

// §7.5.1: the size argument of new[] is a constant expression. §11.2.1 admits a
// parameter as a constant operand, so the size may be a parameter reference
// rather than a literal. The existing tests all size with an integer literal;
// this exercises the parameter-sized path, resolving the operand to the
// parameter's value at run time.
TEST(DynamicArrayNewSimulation, NewSizeFromParameter) {
  auto v = RunAndGet(
      "module t;\n"
      "  parameter int N = 3;\n"
      "  int d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[N];\n"
      "    result = d.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

// §7.5.1: the new[] constructor applies to a dynamic array of any element type,
// not only int. Here the element type is a logic [7:0] vector and the
// initialization array is another dynamic array of the same element type; the
// leading elements are copied, so d[1] is the second source element preserved
// at its 8-bit value. This is the only end-to-end test exercising a non-int
// element type through the new[](init) copy path.
TEST(DynamicArrayNewSimulation, NewNonIntElementTypeCopiesElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] src[] = '{8'hAA, 8'hBB, 8'hCC};\n"
      "  logic [7:0] d[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[2](src);\n"
      "    result = d[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xBBu);
}

// §7.5.1: a dynamic array declaration may use the new[] constructor as its
// declaration-assignment right-hand side. These exercise the lowerer's
// declaration-initializer path rather than a procedural blocking assignment.
TEST(DynamicArrayNewSimulation, DeclNewSizesArray) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = new[4];\n"
      "  int result;\n"
      "  initial result = d.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

TEST(DynamicArrayNewSimulation, DeclNewDefaultInitializesElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = new[4];\n"
      "  int result;\n"
      "  initial result = d[2];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0u);
}

TEST(DynamicArrayNewSimulation, DeclNewWithInitCopiesElements) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20, 30};\n"
      "  int d[] = new[3](src);\n"
      "  int result;\n"
      "  initial result = d[1];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(DynamicArrayNewSimulation, DeclNewNegativeSizeIsError) {
  // §7.5.1: a negative size operand is an error, including in the
  // declaration-assignment form lowered at initialization.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[] = new[-1];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "dynamic array new[] size is negative", 2,
                            "7.5.1"));
}

// §7.5.1: it shall be an error if the size operand is negative, and the report
// a procedural `d = new[n]` raises names §7.5.1.
TEST(DynamicArrayNewSimulation, ProceduralNegativeSizeNames7_5_1) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[];\n"
      "  int n;\n"
      "  initial begin\n"
      "    n = -3;\n"
      "    d = new[n];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "dynamic array new[] size is negative", 6,
                            "7.5.1"));
}

// §7.5.1: the declaration-assignment form is lowered on its own path and
// reaches the same rule, so its report names the same subclause.
TEST(DynamicArrayNewSimulation, DeclNegativeSizeNames7_5_1) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[] = new[-2];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "dynamic array new[] size is negative", 2,
                            "7.5.1"));
}

// §7.5.1: "The new constructor sets the size of a dynamic array and
// initializes its elements", and "In either case, if the new constructor call
// does not specify an initialization expression, the elements are initialized
// to the default value for their type". Elements, plural: §6.8 makes each one
// "an abstraction of a data storage element" that "shall store a value from
// one assignment to the next", so `d = new[3]` owes the array three storage
// elements rather than one value read three times.
//
// The grow arm reaches the size through std::vector::resize(n, value), and
// resize copy-constructs every element it appends from the single value it
// was handed. Logic4Vec copies its `words` pointer and not the words, so all
// three entries come back naming one buffer, the one MakeLogic4VecVal
// allocated for the fill value: a writer that later deposits into d[0] in
// place would be read back through d[1] and d[2] as well. The three pointers
// standing pairwise distinct is the whole of the claim, since equal bits read
// equal by construction on a shared buffer. The zeroes beside them are what
// keeps the case from passing on three elements the run never initialized at
// all, the default value for `int` being the one the clause names.
TEST(DynamicArrayNewSimulation, NewWithoutInitGivesEachElementItsOwnWords) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[];\n"
      "  initial d = new[3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* d = f.ctx.FindQueue("d");
  ASSERT_NE(d, nullptr);
  ASSERT_EQ(d->elements.size(), 3u);
  ASSERT_NE(d->elements[0].words, nullptr);
  ASSERT_NE(d->elements[1].words, nullptr);
  ASSERT_NE(d->elements[2].words, nullptr);
  EXPECT_NE(d->elements[0].words, d->elements[1].words);
  EXPECT_NE(d->elements[1].words, d->elements[2].words);
  EXPECT_NE(d->elements[0].words, d->elements[2].words);
  EXPECT_EQ(d->elements[0].ToUint64(), 0u);
  EXPECT_EQ(d->elements[1].ToUint64(), 0u);
  EXPECT_EQ(d->elements[2].ToUint64(), 0u);
}

// §7.5.1 on the other store the constructor has: "The optional initialization
// expression is used to initialize the dynamic array", and "Resizing or
// reinitializing a previously initialized dynamic array using new is
// destructive; no preexisting array data is preserved (unless reinitialized
// with its old contents -- see preceding), and all preexisting references to
// array elements become outdated". A destination element left sharing a
// buffer with a live source element is exactly such a preexisting reference
// that did not become outdated: `s` goes on naming the storage `d` was just
// given, and a later write through either name would be read back through the
// other.
//
// CopyNewInit finishes with a plain per-element Logic4Vec assignment, which
// carries the `words` pointer over, so `new[2](s)` hands each position of `d`
// the buffer the matching position of `s` still holds. ExpectOwnWordsCopy is
// what makes the storage-identity claim and compares both planes of every
// word alongside it; the second position is claimed on the pointer alone
// because the helper has already established the shape. Reading the literals
// back afterwards says the copy delivered the source values rather than
// leaving `d` empty of them, and the two source values differ, so a run that
// filled both positions from one entry fails here too.
TEST(DynamicArrayNewSimulation, NewWithInitGivesDestinationItsOwnWords) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int s[];\n"
      "  int d[];\n"
      "  initial begin\n"
      "    s = new[2];\n"
      "    s[0] = 32'h1234_5678;\n"
      "    s[1] = 32'h0BAD_F00D;\n"
      "    d = new[2](s);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* s = f.ctx.FindQueue("s");
  ASSERT_NE(s, nullptr);
  ASSERT_EQ(s->elements.size(), 2u);
  auto* d = f.ctx.FindQueue("d");
  ASSERT_NE(d, nullptr);
  ASSERT_EQ(d->elements.size(), 2u);
  ASSERT_NO_FATAL_FAILURE(ExpectOwnWordsCopy(s->elements[0], d->elements[0]));
  ASSERT_NE(d->elements[1].words, nullptr);
  EXPECT_NE(d->elements[1].words, s->elements[1].words);
  EXPECT_EQ(d->elements[0].words[0].aval, 0x12345678u);
  EXPECT_EQ(d->elements[1].words[0].aval, 0x0BADF00Du);
}

}  // namespace
