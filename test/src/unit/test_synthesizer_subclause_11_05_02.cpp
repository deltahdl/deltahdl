#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// Every case below fails on a run that answers a netlist and reports nothing
// for an assignment whose target the synthesizer builds nothing for.
// `SynthLower::LowerContAssign` and `SynthLower::LowerAssignStmt` in
// src/synthesizer/synth_lower.cpp each return without touching the graph when
// the target is not an `ExprKind::kIdentifier`, and
// `SynthLower::LowerSelectTarget` in src/synthesizer/synth_lower_select.cpp
// returns when `SynthLower::ResolveSelect` answers a run of zero bits. None of
// them sets `lowering_incomplete_`, so `SynthLower::Lower` answers a graph that
// never drives the signal the source drives and the run reports success.
//
// `SynthLower::LowerStmt` in src/synthesizer/synth_lower.cpp already does the
// opposite for a statement it has no lowering for: it sets
// `lowering_incomplete_` and reports, and its comment says the location is what
// tells the reader which statement went missing.

// The test fails on a run that drops an assignment to an element of an unpacked
// array and reports nothing. §11.5.2 defines array addressing,
// `mem_name[addr_expr]`, and this synthesizer builds nothing for it in either
// direction. The case separates that from the §11.5.1 select the same syntax is
// written with, which does lower.
TEST(ArrayAddressing,
     AssignToAnUnpackedArrayElementIsReportedRatherThanDropped) {
  SynthFixture f;
  const auto* mod = ElaborateSrc(f,
                                 "module m(input [7:0] a, output logic [7:0] "
                                 "y);\n"
                                 "  logic [7:0] mem [0:3];\n"
                                 "  always_comb begin\n"
                                 "    y = a;\n"
                                 "    mem[0] = a;\n"
                                 "  end\n"
                                 "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment target has no lowering", 5, ""));
}

// The test fails on a fix that reports only what `SynthLower::IsVectorSelect`
// refuses by name and passes over a base that is itself an
// `ExprKind::kSelect`. Such a fix is passed by
// ArrayAddressing.AssignToAnUnpackedArrayElementIsReportedRatherThanDropped,
// whose target names the array itself.
TEST(ArrayAddressing,
     AssignToASelectWhoseBaseIsNotANameIsReportedRatherThanDropped) {
  SynthFixture f;
  const auto* mod = ElaborateSrc(f,
                                 "module m(input [7:0] a, output logic [7:0] "
                                 "y);\n"
                                 "  logic [7:0] mem [0:3];\n"
                                 "  always_comb begin\n"
                                 "    y = a;\n"
                                 "    mem[0][1] = a;\n"
                                 "  end\n"
                                 "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment target has no lowering", 5, ""));
}

}  // namespace
