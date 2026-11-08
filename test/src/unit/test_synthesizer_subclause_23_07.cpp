#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

namespace {

TEST(DottedNameSynthesis, StructMemberSelectIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module t(input logic [15:0] s, output logic [7:0] y);\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  assign p = s;\n"
      "  assign y = p.hi;\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a member of a packed structure has no lowering in "
                            "the synthesizer",
                            5, "7.2.1"));
}

TEST(DottedNameSynthesis, NestedStructMemberSelectIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module t(input logic [15:0] s, output logic [7:0] y);\n"
      "  typedef struct packed { logic [7:0] x; } inner_t;\n"
      "  typedef struct packed { inner_t sub; logic [7:0] pad; } outer_t;\n"
      "  outer_t o;\n"
      "  assign o = s;\n"
      "  assign y = o.sub.x;\n"
      "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a member of a packed structure has no lowering in "
                            "the synthesizer",
                            6, "7.2.1"));
}

TEST(DottedNameSynthesis,
     DottedNamesSharingAMemberNameAreToldApartByTheirFirstComponent) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module child;\n"
      "  logic [7:0] sig;\n"
      "  assign sig = 8'h2a;\n"
      "endmodule\n"
      "module top(input logic [15:0] s, output logic [7:0] a, output logic "
      "[7:0] b);\n"
      "  typedef struct packed { logic [7:0] sig; logic [7:0] pad; } pair_t;\n"
      "  pair_t p;\n"
      "  child c1();\n"
      "  assign p = s;\n"
      "  assign a = p.sig;\n"
      "  assign b = c1.sig;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a member of a packed structure has no lowering in "
                            "the synthesizer",
                            10, "7.2.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a hierarchical name has no lowering in the "
                            "synthesizer",
                            11, "23.6"));
}

}  // namespace
