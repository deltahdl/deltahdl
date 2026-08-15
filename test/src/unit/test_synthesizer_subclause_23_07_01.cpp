
#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

namespace {

TEST(ScopeResolutionPrefixSynthesis, PackagePrefixParamSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "package pkg;\n"
                           "  parameter int WIDTH = 8;\n"
                           "endpackage\n"
                           "module t(input logic [pkg::WIDTH-1:0] a,\n"
                           "         output logic [pkg::WIDTH-1:0] y);\n"
                           "  assign y = a;\n"
                           "endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

// The assertion names §23.7.1 because `pkg::level` is a name written with the
// scope resolution operator rather than a member of a packed structure.
// §23.7.1 defines what this source writes: "A name with a package or class
// scope resolution prefix (::) shall always resolve in a downwards manner and
// shall never be subject to the upwards resolution rules in 23.8. If the
// prefix name can be resolved using the normal scope resolution rules, the
// '::' shall denote the class scope resolution operator. Otherwise the '::'
// shall denote the package scope resolution operator." Parser::MakeMemberAccess
// in src/parser/expr_parser.cpp builds this name as ExprKind::kMemberAccess and
// records the operator in Expr::is_scope_resolution, and it builds the member
// select `p.hi` and the hierarchical name `c1.sig` as that same kind, so
// SynthLower is what has to tell the three apart before it reports one. This
// case fails while SynthLower reports the §7.2.1 packed-structure message for a
// name written with `::`, which is what it reports today.
//
// The source reads a package variable on the right-hand side of a continuous
// assignment, because that is a position the elaborator hands to
// SynthLower::LowerExprBit unevaluated. BuildContAssignFor in
// src/elaborator/elaborator_cont_assign.cpp writes the parser's Expr* into
// RtlirContAssign::rhs (src/elaborator/rtlir.h) and evaluates nothing, and
// SynthLower::LowerExprBit switches on Expr::kind with no constant folding
// ahead of it. ScopeResolutionPrefixSynthesis.PackagePrefixParamSynthesizes
// above writes `pkg::WIDTH` in a packed range instead, which the elaborator
// evaluates into a width, so that name reaches no synthesizer report. `level`
// is a package variable rather than a parameter, so it is not a constant
// expression in any position and no folding can reach it.
TEST(ScopeResolutionPrefixSynthesis,
     PackageVariableReadInAssignmentIsReported) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "package pkg;\n"
                           "  logic [7:0] level;\n"
                           "endpackage\n"
                           "module t(output logic [7:0] y);\n"
                           "  assign y = pkg::level;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  (void)synth.Lower(mod);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a name with a scope resolution operator prefix "
                            "has no lowering in the synthesizer",
                            5, "23.7.1"));
}

}  // namespace
