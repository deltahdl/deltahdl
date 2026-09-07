#include <cstdint>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// §18.17.7 declares a production's formal arguments as a task prototype
// declares them -- "the syntax for declaring the arguments to a production is
// similar to a task prototype" -- so a formal written with a typedef name is an
// object of the type that name stands for (§6.18) and holds the width that type
// declares. The cases below are that width alone; the return type's width is
// test_simulator_subclause_18_17_07b.cpp and the rest of the clause, which
// value reaches which variable, is test_simulator_subclause_18_17_07a.cpp.
//
// Every case here passes a value the declared type is too narrow to hold, so
// that §10.7's truncation is what the reading distinguishes. A formal of
// exactly 32 bits, or a value that fits the type, reads the same whether the
// run honoured the declared width or fell back to the 32-bit carrier the
// unsized formal used to get.

// A formal bound from an actual argument. `8'hFF` is self-determined at eight
// bits, so an unsized formal took the literal's own width and read 255; the
// four bits `nib` declares read 15.
TEST(RandseqFormalWidthSim, TypedefNameFormalIsSizedByTheTypeItNames) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  typedef bit [3:0] nib;\n"
                         "  int r;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    randsequence(main)\n"
                         "      main : gen(8'hFF) ;\n"
                         "      gen( nib p ) : { r = p; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 15u);
}

// §18.17.7's own example gives a production a defaulted formal and generates it
// with no argument, so the default is a second way into the formal and is
// evaluated at a separate site from the actual above. The same 8'hFF written as
// the default has to be truncated by the same rule.
TEST(RandseqFormalWidthSim, TypedefNameFormalSizesItsOwnDefaultValue) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  typedef bit [3:0] nib;\n"
                         "  int r;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    randsequence(main)\n"
                         "      main : gen ;\n"
                         "      gen( nib p = 8'hFF ) : { r = p; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 15u);
}

// The narrow cases above cannot say the declared width is honoured in the other
// direction: a formal clamped to the 32-bit carrier would truncate 8'hFF to 15
// too. `wide` is forty bits, so its value spans two words of the carrier and
// the three answers separate. 48'hFFFF00000001 kept whole reads
// 281470681743361, clamped to 32 bits reads 1, and truncated to the forty bits
// the type declares reads 1095216660481 -- which has bits set above the first
// word, so the high word survives rather than being masked away.
TEST(RandseqFormalWidthSim, TypedefNameFormalWiderThanOneWordKeepsItsHighBits) {
  SimFixture f;
  uint64_t r = RunModule(f,
                         "module t;\n"
                         "  typedef bit [39:0] wide;\n"
                         "  logic [63:0] r;\n"
                         "  initial begin\n"
                         "    r = 0;\n"
                         "    randsequence(main)\n"
                         "      main : gen(48'hFFFF00000001) ;\n"
                         "      gen( wide p ) : { r = p; } ;\n"
                         "    endsequence\n"
                         "  end\n"
                         "endmodule\n",
                         "r");
  EXPECT_EQ(r, 1095216660481ull);
}

}  // namespace
