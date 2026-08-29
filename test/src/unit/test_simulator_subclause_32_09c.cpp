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
// The design declares its module path in the cell the SDF file names, and the
// path is read back off the manager the run installed --
// SimContext::GetSpecifyManager, filled by Lowerer::Lower through
// SimContext::AcquireSpecifyManager -- rather than off a standalone manager
// bound over the top of it. RegisterSpecifyBlocks in
// src/simulator/specify_register.cpp files instance u's path under the
// hierarchical prefix "u.", which is what the annotation the SDF cell
// (INSTANCE dut/u) carries has to reach; issue #3387 is that it did not, the
// annotation having been keyed on the two port names alone.
//
// The SDF triple is 41:52:63. The three differ from each other and from the 0
// the declared module path starts at, so an annotation that never happened and
// an annotation that took the wrong member are each told apart from the right
// one. The path is found by its instance prefix rather than by a lookup that
// answers 0 when it finds nothing, so a case reports a missing path as a
// missing path.

#include <gtest/gtest.h>

#include <cstdint>
#include <fstream>
#include <ios>
#include <string>

#include "common/types.h"
#include "fixture_sdf_design.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

// The design's one module path is declared by mtm_leaf, the cell the SDF file's
// CELL record names, and instantiated once as u below dut. dut is the top, so
// the scope a $sdf_annotate call naming no module_instance operand works from
// is "dut" and the SDF instance path dut/u names u below it.
std::string MtmDesign(const std::string& sdf_path) {
  return "module mtm_leaf(input X, output Y);\n"
         "  specify\n"
         "    (X => Y) = 0;\n"
         "  endspecify\n"
         "endmodule\n"
         "module dut;\n"
         "  logic y_out;\n"
         "  mtm_leaf u(1'b0, y_out);\n"
         "  initial $sdf_annotate(\"" +
         sdf_path +
         "\");\n"
         "endmodule\n";
}

// The delay instance u's module path holds after a run whose only $sdf_annotate
// operand is the file name, with `mode` established on the context beforehand.
// Each case below differs from the others in that one argument.
uint64_t AnnotatedDelayUnderMode(const std::string& stem, DelayMode mode) {
  const std::string kSdfPath = "/tmp/delta_c32_09c_" + stem + ".sdf";
  std::ofstream sdf(kSdfPath, std::ios::trunc);
  sdf << "(DELAYFILE (CELL (CELLTYPE \"mtm_leaf\") (INSTANCE dut/u) "
         "(DELAY (ABSOLUTE (IOPATH X Y (41:52:63))))))";
  sdf.close();

  SdfDesign under_test;
  if (!under_test.Lower(MtmDesign(kSdfPath))) {
    ADD_FAILURE() << "the design did not reach the lowerer, so nothing ran";
    return 0;
  }
  SpecifyManager* installed = under_test.f.ctx.GetSpecifyManager();
  if (installed == nullptr) {
    ADD_FAILURE() << "the run installed no specify manager to annotate onto";
    return 0;
  }
  under_test.f.ctx.SetDelayMode(mode);
  under_test.f.scheduler.Run();

  for (const auto& pd : installed->GetPathDelays()) {
    if (pd.inst_prefix == "u." && pd.dst_port == "Y") return pd.delays[0];
  }
  ADD_FAILURE() << "instance u declared no module path ending at Y";
  return 0;
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
