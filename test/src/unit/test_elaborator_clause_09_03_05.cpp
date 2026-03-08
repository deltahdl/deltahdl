// Non-LRM tests

#include "fixture_elaborator.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

// §9.3.5: Statement label on assignment elaborates.
TEST(ElabClause09_03_05, LabeledAssignmentElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    my_label: x = 42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.3.5: Statement label on begin block (equivalent to block name).
TEST(ElabClause09_03_05, LabelOnBeginBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    blk_label: begin\n"
      "      x = 42;\n"
      "    end : blk_label\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.3.5: Statement label on fork block (equivalent to block name).
TEST(ElabClause09_03_05, LabelOnForkBlockElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    fork_label: fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join : fork_label\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.3.5: Label on if statement elaborates.
TEST(ElabClause09_03_05, LabelOnIfElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    check_label: if (1) x = 42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.3.5: Label on for loop elaborates.
TEST(ElabClause09_03_05, LabelOnForLoopElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    loop_label: for (int i = 0; i < 10; i = i + 1)\n"
      "      x = i;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
