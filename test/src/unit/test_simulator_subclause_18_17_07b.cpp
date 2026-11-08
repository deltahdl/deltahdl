#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"

using namespace delta;

namespace {

TEST(RandseqReturnWidthSim, TypedefNameReturnTypeSizesTheImplicitVariable) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  typedef bit [3:0] nib;\n"
                         "  int r;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    randsequence(main)\n"
                         "      void main : v { r = v; } ;\n"
                         "      nib v : { return 8'hFF; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 15u);
}

TEST(RandseqReturnWidthSim, TypedefNameReturnTypeSizesARandJoinOperand) {
  SimFixture f;
  auto [r1, r2] = RunModuleTwoVars(f,
                                   "module t;\n"
                                   "  typedef bit [3:0] nib;\n"
                                   "  int r1, r2;\n"
                                   "  initial begin\n"
                                   "    r1 = 0; r2 = 0;\n"
                                   "    randsequence(main)\n"
                                   "      void main : rand join v w := 1 "
                                   "{ r1 = v; r2 = w; };\n"
                                   "      nib v : { return 8'hFF; };\n"
                                   "      nib w : { return 8'hF7; };\n"
                                   "    endsequence\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "r1", "r2");
  EXPECT_EQ(r1, 15u);
  EXPECT_EQ(r2, 7u);
}

TEST(RandseqReturnWidthSim,
     TypedefNameReturnTypeSizesEachImplicitArrayElement) {
  SimFixture f;
  auto [r1, r2] = RunModuleTwoVars(f,
                                   "module t;\n"
                                   "  typedef bit [3:0] nib;\n"
                                   "  int r1, r2;\n"
                                   "  initial begin\n"
                                   "    r1 = 0; r2 = 0;\n"
                                   "    randsequence(main)\n"
                                   "      void main : v v "
                                   "{ r1 = v[1]; r2 = v[2]; } ;\n"
                                   "      nib v : { return 8'hFF; } ;\n"
                                   "    endsequence\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "r1", "r2");
  EXPECT_EQ(r1, 15u);
  EXPECT_EQ(r2, 15u);
}

}  // namespace
