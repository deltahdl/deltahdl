#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SequentialBlockElaboration, NestedSeqBlocksElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a, b, c;\n"
      "  initial begin\n"
      "    begin\n"
      "      a = 10;\n"
      "      b = 20;\n"
      "    end\n"
      "    c = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequentialBlockElaboration, SeqBlockWithVarDeclElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    int local_var;\n"
      "    local_var = 42;\n"
      "    x = local_var;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, BeginEndInsideForkElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        a = 1;\n"
      "        b = 0;\n"
      "      end\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StatementBlockElaboration, NestedSeqBlockFollowedByStatement) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    begin\n"
      "      a = 10;\n"
      "    end\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StatementBlockElaboration, ForkInsideSeqBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "    c = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StatementBlockElaboration, SeqBlockInsideForkElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        a = 1;\n"
      "        b = 0;\n"
      "      end\n"
      "      c = 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StatementBlockElaboration, DeeplyNestedBlocksElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    begin\n"
      "      begin\n"
      "        begin\n"
      "          x = 42;\n"
      "        end\n"
      "      end\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, NestedForkElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c;\n"
      "  initial begin\n"
      "    fork\n"
      "      begin\n"
      "        fork\n"
      "          a = 1;\n"
      "          b = 0;\n"
      "        join\n"
      "      end\n"
      "      c = 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BlockNameElaboration, NamedSeqBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial begin : blk\n"
      "    x = 42;\n"
      "  end : blk\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BlockNameElaboration, NamedForkBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    fork : par_blk\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join : par_blk\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, ForkInsideAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always_comb begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ParallelBlockElaboration, ForkInsideAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, q, d;\n"
      "  always_latch begin\n"
      "    fork\n"
      "      q = d;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ParallelBlockElaboration, NestedForkInsideAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  always_comb begin\n"
      "    begin\n"
      "      fork\n"
      "        a = 1;\n"
      "      join\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
