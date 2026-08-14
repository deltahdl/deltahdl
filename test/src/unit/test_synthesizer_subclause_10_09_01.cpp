#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// What the synthesizer answers for each matching rule §10.9.1 states, over an
// array. §10.9.1 rules that in an array assignment pattern "The expressions
// shall match element for element, and the braces shall match the array
// dimensions", gives the replication in which "Each replication shall represent
// an entire single dimension", gives the `default` keyword for setting "array
// elements to a value without having to keep track of how many members there
// are", and states the index:value rule as "An index:value specifies an
// explicit value for a keyed element index". One case per rule below.
//
// Until this change this file wrote no assignment pattern at all. It held an
// unpacked array declaration and two continuous assignments to its elements,
// `assign arr[0] = 8'hAA;` and `assign arr[1] = 8'hBB;`, which is the §11.5.2
// array addressing test/src/unit/test_synthesizer_subclause_11_05_02.cpp
// covers, and its one case asserted the assignment-target report. No brace
// reached the synthesizer from here.
//
// Every form below reaches SynthLower::LowerExprBit in
// src/synthesizer/synth_lower.cpp as ExprKind::kAssignmentPattern, which
// NonSynthExprRule in the same file reports under §10.9, so every case asserts
// a refusal rather than the element values the rule produces. This is the
// array half of what test/src/unit/test_synthesizer_subclause_10_09.cpp covers
// over a bit vector, and the type-prefixed form that file writes is
// ExprKind::kCast rather than ExprKind::kAssignmentPattern.

// The positional rule: the expressions match element for element and the braces
// match the array dimensions.
TEST(ArrayPatternSynth, PositionalPatternOverAnArrayIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] arr [0:2];\n"
                           "  assign arr = '{8'hAA, 8'hBB, 8'hCC};\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment pattern has no lowering in the "
                            "synthesizer",
                            3, "10.9"));
}

// The index:value rule, which names the element rather than counting to it.
// Parser::ParseAssignmentPattern records the keys on the same
// ExprKind::kAssignmentPattern node the positional form above builds, so a
// lowering written for the positional form alone would reach this one and
// answer with whatever it made of an unkeyed item list.
TEST(ArrayPatternSynth, IndexKeyedPatternOverAnArrayIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] arr [0:1];\n"
                           "  assign arr = '{0: 8'h11, 1: 8'h22};\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment pattern has no lowering in the "
                            "synthesizer",
                            3, "10.9"));
}

// The default:value rule, which "applies to elements or subarrays that are not
// matched by either index or type key". Here it matches every element, so the
// pattern carries one item for an array of four and the item count says
// nothing about the element count -- the case above and this one differ in
// that as well as in the key.
TEST(ArrayPatternSynth, DefaultKeyedPatternOverAnArrayIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] arr [0:3];\n"
                           "  assign arr = '{default: 8'h42};\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment pattern has no lowering in the "
                            "synthesizer",
                            3, "10.9"));
}

// The replication §10.9.1 borrows from §11.4.12.1, where "Each replication
// shall represent an entire single dimension". §11.4.12.1 replication over a
// bit vector is a lowering this synthesizer does have, in
// SynthLower::LowerReplicateBit, so this case is what tells the replication
// inside braces from the one outside them: the braces make the node
// ExprKind::kAssignmentPattern rather than ExprKind::kReplicate, and it is
// reported.
TEST(ArrayPatternSynth, ReplicatedPatternOverAnArrayIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] arr [0:2];\n"
                           "  assign arr = '{3{8'hFF}};\n"
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
