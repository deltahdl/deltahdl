#include <cstddef>
#include <cstdint>
#include <vector>

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

// §7.5.1: `new[n]` with no initialization expression owes the array n storage
// elements rather than one value read n times -- "the elements are
// initialized to the default value for their type", each of them, and §6.8
// makes each "an abstraction of a data storage element" that "shall store a
// value from one assignment to the next". What a test of that asserts is that
// no two entries name one buffer, since equal bits cannot tell a copy from a
// shared buffer: a shared buffer reads equal by construction. The default
// value read back beside the pointers is what stops a case passing on
// elements the run never initialized at all. Both callers declare `int`, whose
// default value under Table 6-7 is 0.
//
// Both spellings of the constructor make this claim and reach the store
// through different code, so it is written once here and made twice. A fatal
// assertion inside a helper returns from the helper rather than from the
// test, so callers wrap the call in ASSERT_NO_FATAL_FAILURE.
void ExpectDefaultElementsOwnWords(const QueueObject* q, size_t n) {
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), n);
  for (size_t i = 0; i < n; ++i) {
    SCOPED_TRACE(testing::Message() << "element " << i);
    ASSERT_NE(q->elements[i].words, nullptr);
    EXPECT_EQ(q->elements[i].ToUint64(), 0u);
    for (size_t j = 0; j < i; ++j)
      EXPECT_NE(q->elements[i].words, q->elements[j].words)
          << "shares a buffer with element " << j;
  }
}

// §7.5.1 on the constructor's other store: "The optional initialization
// expression is used to initialize the dynamic array", and "Resizing or
// reinitializing a previously initialized dynamic array using new is
// destructive; no preexisting array data is preserved (unless reinitialized
// with its old contents -- see preceding), and all preexisting references to
// array elements become outdated". A destination entry left sharing a buffer
// with a live source entry is exactly such a preexisting reference that did
// not become outdated: the source goes on naming the storage the destination
// was just given, and a later write through either name would be read back
// through the other.
//
// ExpectOwnWordsCopy carries the storage-identity claim at every position and
// compares both planes of every word beside it. The expected values are what
// says the copy delivered the source's contents rather than leaving the
// destination at the default, and callers pass values that differ from each
// other, so a run that filled every position from one entry fails here too.
// The same ASSERT_NO_FATAL_FAILURE requirement applies as above.
void ExpectElementsCopiedOwningWords(const QueueObject* src,
                                     const QueueObject* dst,
                                     const std::vector<uint64_t>& expected) {
  ASSERT_NE(src, nullptr);
  ASSERT_NE(dst, nullptr);
  ASSERT_EQ(src->elements.size(), expected.size());
  ASSERT_EQ(dst->elements.size(), expected.size());
  for (size_t i = 0; i < expected.size(); ++i) {
    SCOPED_TRACE(testing::Message() << "element " << i);
    ASSERT_NO_FATAL_FAILURE(
        ExpectOwnWordsCopy(src->elements[i], dst->elements[i]));
    EXPECT_EQ(dst->elements[i].ToUint64(), expected[i]);
  }
}

// The blocking-procedural spelling of `new[n]`, against the two claims the
// helpers above make. The grow arm reached the size through
// std::vector::resize(n, value), which copy-constructs every element it
// appends from the single value it was handed; a Logic4Vec copy carries the
// `words` pointer and not the words, so all three entries came back naming
// the one buffer MakeLogic4VecVal had allocated, and a deposit into d[0] in
// place would have been read back through d[1] and d[2] as well.
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
  ASSERT_NO_FATAL_FAILURE(
      ExpectDefaultElementsOwnWords(f.ctx.FindQueue("d"), 3u));
}

// CopyNewInit finished with a plain per-element Logic4Vec assignment, which
// carries the `words` pointer over, so `new[2](s)` handed each position of `d`
// the buffer the matching position of `s` still holds.
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
  ASSERT_NO_FATAL_FAILURE(ExpectElementsCopiedOwningWords(
      f.ctx.FindQueue("s"), f.ctx.FindQueue("d"), {0x12345678u, 0x0BADF00Du}));
}

// §7.5.1 puts the two spellings of the constructor under one rule: it "may
// appear in place of the right-hand side expression of variable declaration
// assignments and blocking procedural assignments when the left-hand side
// indicates a dynamic array". The declaration half is lowered rather than
// executed, so its two stores are its own and the pair above does not reach
// them. This one is LowerDynArrayNewInit's std::vector::assign(n, value),
// which copy-constructs every slot it makes from the one value it is handed,
// so `int d[] = new[3];` held one buffer read three times.
TEST(DynamicArrayNewSimulation, DeclNewWithoutInitGivesEachElementItsOwnWords) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d[] = new[3];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  ASSERT_NO_FATAL_FAILURE(
      ExpectDefaultElementsOwnWords(f.ctx.FindQueue("d"), 3u));
}

// The declaration half's copy loop, which was the same plain per-element
// Logic4Vec assignment CopyNewInit ended with. The source array is filled
// from an assignment-pattern declaration initializer, which evaluates each
// item separately and so gives `s` two buffers of its own to be shared out.
TEST(DynamicArrayNewSimulation, DeclNewWithInitGivesDestinationItsOwnWords) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int s[] = '{32'h1234_5678, 32'h0BAD_F00D};\n"
      "  int d[] = new[2](s);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  ASSERT_NO_FATAL_FAILURE(ExpectElementsCopiedOwningWords(
      f.ctx.FindQueue("s"), f.ctx.FindQueue("d"), {0x12345678u, 0x0BADF00Du}));
}

}  // namespace
