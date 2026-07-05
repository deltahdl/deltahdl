#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §18.13.1: every $urandom claim below is a runtime rule realized by the
// simulator's PRNG evaluation (EvalPrngCall / SimContext::Urandom32 /
// SeedUrandom). Each test builds the call from real source in one of the
// syntactic positions the LRM example uses -- a bit-select target, a
// concatenation element, a masked operand, a seeded/plain call -- and drives it
// through parse -> elaborate -> lower -> run, observing the committed variable
// value rather than a hand-built call node.

// "The function returns a new 32-bit random number ... The number shall be
// unsigned." A single 32-bit draw assigned to a 64-bit target must ZERO-extend
// (upper 32 bits stay 0); a signed result would sign-extend and set them once
// any draw has its top bit set. Accumulating the OR of 64 deterministic draws
// (default seed 0 => a fixed sequence) makes at least one top-bit-set draw a
// certainty, so upper == 0 pins down both the 32-bit width and the unsigned
// result through the assignment's own extension path.
TEST(SysTask, UrandomIs32BitUnsignedResult) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [63:0] acc;\n"
      "  logic [63:0] w;\n"
      "  initial begin\n"
      "    acc = 64'd0;\n"
      "    for (int i = 0; i < 64; i = i + 1) begin\n"
      "      w = $urandom;\n"
      "      acc = acc | w;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ASSERT_FALSE(f.has_errors);

  auto* acc = f.ctx.FindVariable("acc");
  ASSERT_NE(acc, nullptr);
  uint64_t v = acc->value.ToUint64();
  // Unsigned + 32-bit: nothing bled above bit 31 across every draw.
  EXPECT_EQ(v >> 32, 0u);
  // The draws actually populated the low 32 bits (not a stuck-at-zero source).
  EXPECT_NE(v & 0xFFFFFFFFu, 0u);
}

// "The RNG shall generate the same sequence of random numbers every time the
// same seed is used." Re-seeding with the same value restarts the identical
// sequence, so two seeded draws with the same seed match.
TEST(SysTask, UrandomSameSeedReplaysSequence) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned a;\n"
      "  int unsigned b;\n"
      "  initial begin\n"
      "    a = $urandom(12345);\n"
      "    b = $urandom(12345);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ASSERT_FALSE(f.has_errors);

  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), b->value.ToUint64());
}

// The seed selects the sequence: two distinct seeds diverge.
TEST(SysTask, UrandomDistinctSeedsDiverge) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned p;\n"
      "  int unsigned q;\n"
      "  initial begin\n"
      "    p = $urandom(1);\n"
      "    q = $urandom(2);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ASSERT_FALSE(f.has_errors);

  auto* p = f.ctx.FindVariable("p");
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(p, nullptr);
  ASSERT_NE(q, nullptr);
  EXPECT_NE(p->value.ToUint64(), q->value.ToUint64());
}

// "a new 32-bit random number each time it is called": the generator advances
// per call, so a seeded draw followed by an unseeded draw yields two different
// numbers.
TEST(SysTask, UrandomAdvancesEachCall) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned x;\n"
      "  int unsigned y;\n"
      "  initial begin\n"
      "    x = $urandom(9);\n"
      "    y = $urandom;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ASSERT_FALSE(f.has_errors);

  auto* x = f.ctx.FindVariable("x");
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(x, nullptr);
  ASSERT_NE(y, nullptr);
  EXPECT_NE(x->value.ToUint64(), y->value.ToUint64());
}

// "The RNG is deterministic. Each time the program executes, it cycles through
// the same random sequence." Two independent runs of the same source, each
// from a fresh unseeded context, draw the identical first value.
TEST(SysTask, UrandomDeterministicAcrossRuns) {
  const char* src =
      "module t;\n"
      "  int unsigned x;\n"
      "  initial x = $urandom;\n"
      "endmodule\n";

  SimFixture f1;
  auto* d1 = ElaborateSrc(src, f1);
  ASSERT_NE(d1, nullptr);
  LowerAndRun(d1, f1);
  ASSERT_FALSE(f1.has_errors);

  SimFixture f2;
  auto* d2 = ElaborateSrc(src, f2);
  ASSERT_NE(d2, nullptr);
  LowerAndRun(d2, f2);
  ASSERT_FALSE(f2.has_errors);

  auto* x1 = f1.ctx.FindVariable("x");
  auto* x2 = f2.ctx.FindVariable("x");
  ASSERT_NE(x1, nullptr);
  ASSERT_NE(x2, nullptr);
  EXPECT_EQ(x1->value.ToUint64(), x2->value.ToUint64());
}

// "The seed can be any integral expression." The sequence is keyed by the seed
// VALUE, not the syntactic form: a literal, a localparam constant, a runtime
// variable, and a constant expression that all evaluate to 7 produce the same
// first draw.
TEST(SysTask, UrandomSeedFormsWithEqualValueMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int P = 7;\n"
      "  int rs;\n"
      "  int unsigned a;\n"
      "  int unsigned b;\n"
      "  int unsigned c;\n"
      "  int unsigned d;\n"
      "  initial begin\n"
      "    rs = 7;\n"
      "    a = $urandom(7);\n"
      "    b = $urandom(P);\n"
      "    c = $urandom(rs);\n"
      "    d = $urandom(3 + 4);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ASSERT_FALSE(f.has_errors);

  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  auto* c = f.ctx.FindVariable("c");
  auto* d = f.ctx.FindVariable("d");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  ASSERT_NE(c, nullptr);
  ASSERT_NE(d, nullptr);
  uint64_t va = a->value.ToUint64();
  EXPECT_EQ(b->value.ToUint64(), va);
  EXPECT_EQ(c->value.ToUint64(), va);
  EXPECT_EQ(d->value.ToUint64(), va);
}

// "The seed can be any integral expression." A module parameter is a distinct
// constant path from a localparam or a bare literal, yet it keys the sequence
// by its value: seeding with a parameter that defaults to 100 replays the same
// first draw as seeding with the literal 100.
TEST(SysTask, UrandomParameterSeedMatchesLiteral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t #(parameter int SEED = 100);\n"
      "  int unsigned via_param;\n"
      "  int unsigned via_literal;\n"
      "  initial begin\n"
      "    via_param = $urandom(SEED);\n"
      "    via_literal = $urandom(100);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ASSERT_FALSE(f.has_errors);

  auto* p = f.ctx.FindVariable("via_param");
  auto* l = f.ctx.FindVariable("via_literal");
  ASSERT_NE(p, nullptr);
  ASSERT_NE(l, nullptr);
  EXPECT_EQ(p->value.ToUint64(), l->value.ToUint64());
}

// The seed argument has type int (32 bits): a wider integral seed expression is
// reduced to its low 32 bits, so a 64-bit seed whose low word is 7 keys the
// same sequence as the literal 7.
TEST(SysTask, UrandomWideSeedReducesToInt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned narrow;\n"
      "  int unsigned wide;\n"
      "  initial begin\n"
      "    narrow = $urandom(7);\n"
      "    wide = $urandom(64'h1_0000_0007);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ASSERT_FALSE(f.has_errors);

  auto* narrow = f.ctx.FindVariable("narrow");
  auto* wide = f.ctx.FindVariable("wide");
  ASSERT_NE(narrow, nullptr);
  ASSERT_NE(wide, nullptr);
  EXPECT_EQ(narrow->value.ToUint64(), wide->value.ToUint64());
}

// LRM example form: a bit-select target -- addr[32:1] = $urandom(254). The
// seeded 32-bit draw lands only in the selected low 32 bits of a bit [64:1]
// vector; the untouched upper half stays 0, and the whole result is
// deterministic across runs because the draw is seeded.
TEST(SysTask, UrandomIntoBitSelectTarget) {
  const char* src =
      "module t;\n"
      "  bit [64:1] addr;\n"
      "  initial begin\n"
      "    addr = 64'd0;\n"
      "    addr[32:1] = $urandom(254);\n"
      "  end\n"
      "endmodule\n";

  SimFixture f1;
  auto* d1 = ElaborateSrc(src, f1);
  ASSERT_NE(d1, nullptr);
  LowerAndRun(d1, f1);
  ASSERT_FALSE(f1.has_errors);

  SimFixture f2;
  auto* d2 = ElaborateSrc(src, f2);
  ASSERT_NE(d2, nullptr);
  LowerAndRun(d2, f2);
  ASSERT_FALSE(f2.has_errors);

  auto* a1 = f1.ctx.FindVariable("addr");
  auto* a2 = f2.ctx.FindVariable("addr");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  uint64_t v = a1->value.ToUint64();
  // Only the low 32 bits were written; the upper half is untouched zero.
  EXPECT_EQ(v >> 32, 0u);
  // A seeded draw replays identically on a second run.
  EXPECT_EQ(v, a2->value.ToUint64());
}

// LRM example form: a concatenation of two draws -- addr = {$urandom,
// $urandom} -- builds a 64-bit value from two independent 32-bit draws. The
// result is deterministic across runs (unseeded default sequence).
TEST(SysTask, UrandomConcatenationBuildsWideValue) {
  const char* src =
      "module t;\n"
      "  logic [63:0] addr;\n"
      "  initial addr = {$urandom, $urandom};\n"
      "endmodule\n";

  SimFixture f1;
  auto* d1 = ElaborateSrc(src, f1);
  ASSERT_NE(d1, nullptr);
  LowerAndRun(d1, f1);
  ASSERT_FALSE(f1.has_errors);

  SimFixture f2;
  auto* d2 = ElaborateSrc(src, f2);
  ASSERT_NE(d2, nullptr);
  LowerAndRun(d2, f2);
  ASSERT_FALSE(f2.has_errors);

  auto* a1 = f1.ctx.FindVariable("addr");
  auto* a2 = f2.ctx.FindVariable("addr");
  ASSERT_NE(a1, nullptr);
  ASSERT_NE(a2, nullptr);
  uint64_t v = a1->value.ToUint64();
  // Both 32-bit halves were populated by the two draws.
  EXPECT_NE(v >> 32, 0u);
  EXPECT_NE(v & 0xFFFFFFFFu, 0u);
  // Deterministic replay of the whole concatenation.
  EXPECT_EQ(v, a2->value.ToUint64());
}

// LRM example form: masking a draw to a narrow field -- number = $urandom & 15
// -- yields a value confined to 4 bits. Declared as bit [3:0], the committed
// result never exceeds 15, and the seeded draw replays across runs.
TEST(SysTask, UrandomMaskedToFourBits) {
  const char* src =
      "module t;\n"
      "  bit [3:0] number;\n"
      "  initial number = $urandom(254) & 15;\n"
      "endmodule\n";

  SimFixture f1;
  auto* d1 = ElaborateSrc(src, f1);
  ASSERT_NE(d1, nullptr);
  LowerAndRun(d1, f1);
  ASSERT_FALSE(f1.has_errors);

  SimFixture f2;
  auto* d2 = ElaborateSrc(src, f2);
  ASSERT_NE(d2, nullptr);
  LowerAndRun(d2, f2);
  ASSERT_FALSE(f2.has_errors);

  auto* n1 = f1.ctx.FindVariable("number");
  auto* n2 = f2.ctx.FindVariable("number");
  ASSERT_NE(n1, nullptr);
  ASSERT_NE(n2, nullptr);
  EXPECT_LE(n1->value.ToUint64(), 15u);
  EXPECT_EQ(n1->value.ToUint64(), n2->value.ToUint64());
}

}  // namespace
