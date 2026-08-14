#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

// Covers the { block_item_declaration } element of the A.6.3 seq_block
// production: a declaration inside begin/end, followed by statements that
// read it and write an enclosing-scope variable. The 9.3.1 sibling file
// covers the prose case of a plain block-local declaration.
TEST(SequentialBlockElaboration, SeqBlockItemDeclarationElaborates) {
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

// Covers the optional block_identifier on both ends of the A.6.3 par_block
// production, fork [ : block_identifier ] ... join_keyword
// [ : block_identifier ]. The 9.3.4 sibling file covers the prose rule that
// a name after the join keyword shall match the name after fork.
TEST(BlockNameElaboration, ParBlockWithBlockIdentifierElaborates) {
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
  // The report stands at the always_comb keyword on line 3, which is the
  // construct the rule forbids the fork inside, not at the fork on line 4.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not contain fork-join "
                            "statements",
                            3, "9.2.2.2.2"));
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
  // As above, the report stands at the always_latch keyword on line 3.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_latch shall not contain fork-join "
                            "statements",
                            3, "9.2.2.2.2"));
}

}  // namespace
