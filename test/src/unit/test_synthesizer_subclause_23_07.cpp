
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

// This case fails when the synthesizer decides a dotted name by anything other
// than the first component of that name. The two dotted names below share the
// member name `sig` and differ only in the name they start from, so a
// discrimination that reads the member name, the depth of the chain or the
// order the assignments were written in gets one of the two wrong. §23.7 is the
// subclause that rules them apart: "The distinguishing aspect of a hierarchical
// name is that the first component of the name matches a scope name while the
// first name component of a member select matches a data object or interface
// port name." `p` is a pair_t variable, so `p.sig` is the member select §7.2.1
// defines. `c1` is an instance of module child, so `c1.sig` is the hierarchical
// name §23.6 defines.
//
// The two ReportedError calls are the claim this case makes. The claim is that
// two dotted names in one module draw two different reports, and one call
// cannot state it. Both names draw the same report while NonSynthExprRule in
// src/synthesizer/synth_lower.cpp gives all of ExprKind::kMemberAccess one
// entry: `p.sig` and `c1.sig` are both that kind, so both are reported as a
// member of a packed structure under §7.2.1 and the second call below is the
// one that fails.
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
