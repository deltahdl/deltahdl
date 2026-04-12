#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParallelBlockElaboration, ForkJoinInInitialElaborates) {
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

TEST(ParallelBlockElaboration, ForkJoinAnyElaborates) {
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

TEST(ParallelBlockElaboration, ForkJoinNoneElaborates) {
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

TEST(ParallelBlockElaboration, EmptyForkJoinElaborates) {
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

TEST(ParallelBlockElaboration, ReturnInForkJoinErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t;\n"
      "    fork\n"
      "      return;\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ParallelBlockElaboration, ReturnInForkJoinAnyErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t;\n"
      "    fork\n"
      "      return;\n"
      "    join_any\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ParallelBlockElaboration, ReturnInForkJoinNoneErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t;\n"
      "    fork\n"
      "      return;\n"
      "    join_none\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ParallelBlockElaboration, ReturnNestedInForkErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t;\n"
      "    fork\n"
      "      begin\n"
      "        return;\n"
      "      end\n"
      "    join\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(ParallelBlockElaboration, ForkWithLocalparamElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      localparam int N = 4;\n"
      "      a = N;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, ForkWithParameterElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      parameter int W = 8;\n"
      "      a = W;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParallelBlockElaboration, ForkWithBeginEndElaborates) {
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
