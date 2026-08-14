#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// The case below fails on a run that answers a netlist and reports nothing for
// an assignment whose target the synthesizer builds nothing for.
// `SynthLower::LowerContAssign` and `SynthLower::LowerAssignStmt` in
// src/synthesizer/synth_lower.cpp each return without touching the graph when
// the target is not an `ExprKind::kIdentifier`, and none of the paths that
// return early sets `lowering_incomplete_`, so `SynthLower::Lower` answers a
// graph that never drives the signal the source drives and the run reports
// success.
//
// `SynthLower::LowerStmt` in src/synthesizer/synth_lower.cpp already does the
// opposite for a statement it has no lowering for: it sets
// `lowering_incomplete_` and reports, and its comment says the location is what
// tells the reader which statement went missing.

// The test fails on a fix that covers `ExprKind::kSelect` alone. §7.2.1 rules
// that "A packed structure is a mechanism for subdividing a vector into
// subfields, which can be conveniently accessed as members", so the target
// names bits of a vector the netlist holds.
TEST(PackedStructTarget, AssignToAStructMemberIsReportedRatherThanDropped) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, output logic [3:0] y);\n"
                   "  typedef struct packed { logic [3:0] f; } s_t;\n"
                   "  s_t p;\n"
                   "  always_comb begin\n"
                   "    y = a;\n"
                   "    p.f = a;\n"
                   "  end\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment target has no lowering", 6, ""));
}

}  // namespace
