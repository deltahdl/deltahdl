#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(BlockNameElaboration, LabeledSeqBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a;\n"
      "  initial begin : my_block\n"
      "    a = 42;\n"
      "  end : my_block\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BlockNameElaboration, NamedForkBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    fork : workers\n"
      "      a = 1;\n"
      "      b = 2;\n"
      "    join : workers\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BlockNameElaboration, NamedBlockWithVarDeclElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin : blk\n"
      "    int x;\n"
      "    x = 42;\n"
      "  end : blk\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BlockNameElaboration, NestedNamedBlocksElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      a = 1;\n"
      "    end : inner\n"
      "  end : outer\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BlockNameElaboration, UnnamedBlockWithDeclElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = 10;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BlockNameElaboration, NamedEmptyBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin : empty\n"
      "  end : empty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
