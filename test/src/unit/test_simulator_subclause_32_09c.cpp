// §32.9 gives $sdf_annotate an mtm_spec operand whose legal values Table 32-5
// lists, and TOOL_CONTROL -- the value that table marks the default, and so the
// value a call naming no mtm_spec has -- is described there as "Annotates the
// value as selected by the simulator". What this simulator selects is what
// SimContext::GetDelayMode answers, which --mintypmax establishes for the whole
// run, so a min:typ:max triple in an SDF file and a §11.11 min:typ:max
// expression in the source cannot end up on different members.
//
// The other two files over §32.9 are test_simulator_subclause_32_09a.cpp, which
// calls the SDF reader and the scaling directly, and
// test_simulator_subclause_32_09b.cpp, which covers the seven operands as they
// are written in a design. The claim here is about the mtm_spec that is not
// written at all, so it needs a delay mode established on the context before
// the run and belongs in neither.
//
// The SDF triple is 41:52:63. The three differ from each other, from the 0 the
// declared module path starts at, and from the 0 SpecifyManager::GetPathDelay
// answers for a path it does not hold, so an annotation that never happened and
// an annotation that took the wrong member are each told apart from the right
// one.

#include <gtest/gtest.h>

#include <cstdint>
#include <fstream>
#include <ios>
#include <string>

#include "common/types.h"
#include "fixture_sdf_design.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// The delay the module path holds after a run whose only $sdf_annotate operand
// is the file name, with `mode` established on the context beforehand. Each
// case below differs from the others in that one argument.
uint64_t AnnotatedDelayUnderMode(const std::string& stem, DelayMode mode) {
  const std::string kSdfPath = "/tmp/delta_c32_09c_" + stem + ".sdf";
  std::ofstream sdf(kSdfPath, std::ios::trunc);
  sdf << "(DELAYFILE (CELL (CELLTYPE \"cell\") (INSTANCE dut/u) "
         "(DELAY (ABSOLUTE (IOPATH X Y (41:52:63))))))";
  sdf.close();

  SdfDesign under_test;
  if (!under_test.Lower("module cell(input I, output O);\n"
                        "endmodule\n"
                        "module dut(input X, output Y);\n"
                        "  cell u(X, Y);\n"
                        "  specify\n"
                        "    (X => Y) = 0;\n"
                        "  endspecify\n"
                        "  initial $sdf_annotate(\"" +
                        kSdfPath +
                        "\");\n"
                        "endmodule\n")) {
    ADD_FAILURE() << "the design did not reach the lowerer, so nothing ran";
    return 0;
  }
  under_test.AddPathDelays(under_test.Top());
  under_test.f.ctx.SetSpecifyManager(&under_test.mgr);
  under_test.f.ctx.SetDelayMode(mode);
  under_test.f.scheduler.Run();
  EXPECT_TRUE(under_test.mgr.HasPathDelay("X", "Y"));
  return under_test.mgr.GetPathDelay("X", "Y");
}

// Table 32-5's TOOL_CONTROL with the simulator selecting the minimum: the first
// member of the SDF triple is what the module path ends up holding.
TEST(SdfToolControlMtm, AbsentMtmSpecAnnotatesTheMinimumWhenTheRunSelectsIt) {
  EXPECT_EQ(AnnotatedDelayUnderMode("min", DelayMode::kMin), 41u);
}

// The same call at the other end of the triple. Nothing but the delay mode
// differs from the case above, so the pair says the annotated member follows
// what the run selected rather than being fixed at one of the three.
TEST(SdfToolControlMtm, AbsentMtmSpecAnnotatesTheMaximumWhenTheRunSelectsIt) {
  EXPECT_EQ(AnnotatedDelayUnderMode("max", DelayMode::kMax), 63u);
}

}  // namespace
