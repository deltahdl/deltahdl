#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

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

TEST(PackedStructTarget, ReadOfAStructMemberIsReportedRatherThanDropped) {
  SynthFixture f;
  const auto* mod = ElaborateSrc(
      f,
      "module m(input [7:0] a, output logic [3:0] y);\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  assign p = a;\n"
      "  assign y = p.hi;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a member of a packed structure has no lowering", 5,
                            "7.2.1"));
}

}  // namespace
