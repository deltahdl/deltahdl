#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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
  EXPECT_EQ(v >> 32, 0u);
  EXPECT_NE(v & 0xFFFFFFFFu, 0u);
}

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

TEST(SysTask, UrandomIntoBitSelectTarget) {
  const char* src =
      "module t;\n"
      "  bit [64:1] addr;\n"
      "  initial begin\n"
      "    addr = 64'd0;\n"
      "    addr[32:1] = $urandom(254);\n"
      "  end\n"
      "endmodule\n";

  uint64_t v = RunTwiceForSameValue(src, "addr");
  EXPECT_EQ(v >> 32, 0u);
}

TEST(SysTask, UrandomConcatenationBuildsWideValue) {
  const char* src =
      "module t;\n"
      "  logic [63:0] addr;\n"
      "  initial addr = {$urandom, $urandom};\n"
      "endmodule\n";

  uint64_t v = RunTwiceForSameValue(src, "addr");
  EXPECT_NE(v >> 32, 0u);
  EXPECT_NE(v & 0xFFFFFFFFu, 0u);
}

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
