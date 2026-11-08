#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(EventTriggerSynthesis, EventTriggerIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  event ev;\n"
                           "  reg x;\n"
                           "  always begin\n"
                           "    -> ev;\n"
                           "    x = 1;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "event trigger is not synthesizable", 5, "15.5.1"));
}

TEST(EventTriggerSynthesis, NonblockingEventTriggerIsRejectedByName) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  event ev;\n"
                           "  reg x;\n"
                           "  always begin\n"
                           "    ->> ev;\n"
                           "    x = 1;\n"
                           "  end\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nonblocking event trigger is not synthesizable", 5,
                            "15.5.1"));
  EXPECT_EQ(FindDiag(f, "event trigger is not synthesizable"), nullptr);
}

}  // namespace
