#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// What the synthesizer answers for the array literal §5.11 defines. §5.11 rules
// that "Array literals are syntactically similar to C initializers, but with
// the replication operator ( {{}} ) allowed", and that "Array literals are
// array assignment patterns or pattern expressions with constant member
// expressions (see 10.9.1)". Each case below writes one of the forms §5.11
// states and asserts the report that form draws.
//
// Until this change this file wrote no array literal at all. It held an
// unpacked array declaration and two continuous assignments to its elements,
// `assign arr[0] = 8'hAA;` and `assign arr[1] = 8'hBB;`, which is the §11.5.2
// array addressing that test/src/unit/test_synthesizer_subclause_11_05_02.cpp
// covers, and its one case asserted the assignment-target report. No `'{`
// reached the synthesizer from here.
//
// Every case asserts a refusal rather than a netlist value. SynthLower::
// LowerExprBit in src/synthesizer/synth_lower.cpp has no lowering for either
// expression kind an array literal arrives as, and NonSynthExprRule in the same
// file reports both.

// §5.11 rules that an array literal "shall have a type, which may be either
// explicitly indicated with a prefix or implicitly indicated by an
// assignment-like context (see 10.8)". Written with no prefix, the literal
// reaches SynthLower::LowerExprBit as ExprKind::kAssignmentPattern, which
// NonSynthExprRule reports under §10.9.
TEST(ArrayLiteralSynth, UntypedArrayLiteralIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] arr [0:1];\n"
                           "  assign arr = '{8'hAA, 8'hBB};\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment pattern has no lowering in the "
                            "synthesizer",
                            3, "10.9"));
}

// The storage the literal is assigned to does not change the answer. §7.4.1
// makes `logic [1:0][7:0] packed_arr` one sixteen-bit signal rather than the
// two elements the case above declares, and SynthLower::MapPorts records only
// the unpacked declaration in unpacked_arrays_, so a target this synthesizer
// can address bit by bit still draws the §10.9 report the literal draws.
TEST(ArrayLiteralSynth, ArrayLiteralOnAPackedTargetIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [1:0][7:0] packed_arr;\n"
                           "  assign packed_arr = '{8'hCC, 8'hDD};\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment pattern has no lowering in the "
                            "synthesizer",
                            3, "10.9"));
}

// The prefix form §5.11 admits, which its example writes as `typedef int
// triple [1:3];` and `triple'{0,1,2}`. Parser::TryParseUserTypeCast builds a
// name followed by `'{` as a cast over the pattern, so the kind that
// SynthLower::LowerExprBit meets is ExprKind::kCast and the report names
// §6.24.1 rather than the §10.9 the two cases above name. A lowering written
// for ExprKind::kAssignmentPattern alone would leave this form answering
// constant zero.
TEST(ArrayLiteralSynth, TypePrefixedArrayLiteralIsReportedUnloweredAsACast) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  typedef int triple [1:3];\n"
                           "  int arr [1:3];\n"
                           "  assign arr = triple'{0, 1, 2};\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a cast has no lowering in the synthesizer", 4,
                            "6.24.1"));
}

// The nested literal §5.11 writes, where "The nesting of braces shall follow
// the number of dimensions" and a replication operator may stand inside them.
// This is §5.11's own example `int n[1:2][1:3] = '{'{0,1,2},'{3{4}}};` written
// as a continuous assignment. The three cases above each write one brace pair
// over one dimension, so none of them reaches the outer
// ExprKind::kAssignmentPattern whose elements are themselves patterns, which is
// the node SynthLower::LowerExprBit meets here.
TEST(ArrayLiteralSynth, NestedArrayLiteralIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  int n [1:2][1:3];\n"
                           "  assign n = '{'{0, 1, 2}, '{3{4}}};\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment pattern has no lowering in the "
                            "synthesizer",
                            3, "10.9"));
}

}  // namespace
