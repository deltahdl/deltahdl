#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// §18.17.7 gives the implicit variable a rule declares for a value-returning
// production "the return type of the production", so a production declared to
// return a user-defined type returns the width that type names and not the
// width of the expression the return statement was written with. The cases
// below are that width alone; test_simulator_subclause_18_17_07a.cpp holds the
// rest of the clause -- which variable an appearance writes, what a rand join
// operand captures, and how a string return is carried.
//
// Every case returns 8'hFF through a four-bit typedef and reads 15. The two
// answers have to differ for the case to say anything: a typedef of exactly 32
// bits, or a value that fits in four, reads the same whether the run honoured
// the declared width or fell back to the 32-bit carrier, and 255 is what the
// fallback reports.

// The ordinary production path, which sizes its slot in ExecRsProduction.
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

// §18.17.5's rand join sizes its operands' slots at a site of its own,
// BuildOneRandJoinSeq, so an operand declared to return a typedef name is a
// separate claim from the ordinary production above. Both operands are read,
// since a case reading one of them cannot show the other was sized; they return
// different values so that neither can stand in for the other, and 8'hF7 reads
// 7 through `nib` against the fallback's 247.
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

// §18.17.7: a production named more than once in a rule is declared as "an
// array where the element type is the return type of the production", so the
// element width is the typedef's too. Naming the production twice takes the
// implicit variable down CreateRuleProductionVariable's array arm, which builds
// the name `v[i]` and creates a variable per appearance rather than the one
// scalar the cases above write, so the width claimed for the scalar is not the
// width claimed here. Both elements are read because either arriving at 255
// would be the fallback.
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
