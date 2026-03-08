// Non-LRM tests

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §9.3.2: fork/join elaborates within an initial process.
TEST(ElabClause09_03_02, ForkJoinInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.3.2: fork/join_any elaborates without errors.
TEST(ElabClause09_03_02, ForkJoinAnyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.3.2: fork/join_none elaborates without errors.
TEST(ElabClause09_03_02, ForkJoinNoneElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.3.2: Empty fork/join elaborates without errors.
TEST(ElabClause09_03_02, EmptyForkJoinElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.3.2: begin-end inside fork creates a single sequential process.
TEST(ElabClause09_03_02, BeginEndInsideForkElaborates) {
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

}  // namespace
