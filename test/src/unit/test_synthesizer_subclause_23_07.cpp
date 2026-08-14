
#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

namespace {

// A member select written with '.' reaches SynthLower::LowerExprBit as
// ExprKind::kMemberAccess, and the synthesizer has no lowering for it, so it
// reports the select under §7.2.1 and SynthLower::Lower answers with nothing.
// The case used to assert only that a graph came back, which held while
// kMemberAccess fell through to constant zero: `y` came out zero rather than
// the top half of `s`, and nothing said so.
//
// The name this case carried, StructMemberSelectSynthesizes, claimed a netlist
// in which `y` carries s[15:8]. To claim that again the lowering would have to
// resolve `p.hi` to the offset and width §7.2.1 gives the member inside the
// packed structure and read those bits of `p`, which is the same computation
// SynthLower::LowerSelectBit performs for a part-select.
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

// A member select through a nested structure is one ExprKind::kMemberAccess
// node built over another, and only the outer one reaches
// SynthLower::LowerExprBit, so the §7.2.1 report stands once at the name the
// chain starts from. The case used to assert only that a graph came back, which
// held while the chain fell through to constant zero.
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

}  // namespace
