#include "fixture_simulator.h"
#include "helpers_lower_run.h"

using namespace delta;

namespace {

// §20.16, Table 20-12 enumerates the sixteen PLA modeling system tasks as the
// combinations of an array_type (sync/async), a logic (and/or/nand/nor), and a
// format (array/plane). At the simulator stage the recognizer decodes exactly
// those three dollar-separated components: a name matching the table is treated
// as a PLA task and dispatched to the array engine, which drives its output
// terms; any other name is not. These tests observe that recognition boundary
// end-to-end -- identical memory and input terms, only the callee name changes.

// §20.16, Table 20-12: a name that is one of the sixteen enumerated tasks is
// recognized and dispatched, so its output term is driven. (The particular
// reduced value is the array-type/logic/format behavior of §20.16.1/.2/.4; here
// it only witnesses that dispatch happened.)
TEST(PlaRecognition, TableNameIsDispatchedAndDrivesOutput) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  initial begin\n"
                           "    out = 1'b0;\n"
                           "    mem[1] = 2'b11;\n"
                           "    in = 2'b11;\n"
                           "    $sync$and$array(mem, in, out);\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  // Recognized: the engine ran and drove the output away from its init value.
  EXPECT_EQ(out, 1u);
}

// §20.16, Table 20-12: a name carrying more than the three
// array_type/logic/format components is not one of the enumerated tasks, so the
// simulator does not recognize it as a PLA task and never invokes the array
// engine. With everything else identical to the accepting case, the output term
// keeps the value it was initialized to.
TEST(PlaRecognition, ExtraComponentNameIsNotDispatched) {
  SimFixture f;
  uint64_t out = RunModule(f,
                           "module t;\n"
                           "  logic [1:2] in;\n"
                           "  logic [1:2] mem [1:1];\n"
                           "  logic [1:1] out;\n"
                           "  initial begin\n"
                           "    out = 1'b0;\n"
                           "    mem[1] = 2'b11;\n"
                           "    in = 2'b11;\n"
                           "    $sync$and$array$extra(mem, in, out);\n"
                           "  end\n"
                           "endmodule\n",
                           "out");
  // Not recognized: the engine never ran, so the output holds its init value.
  EXPECT_EQ(out, 0u);
}

}  // namespace
