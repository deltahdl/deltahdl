#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// What the synthesizer answers for the built-in method §5.13 defines. §5.13
// rules that "SystemVerilog uses a C++ -like class method calling syntax, in
// which a subroutine is called using the dot notation (.)", writes that call as
// `object.task_or_function()`, gives `dynamic_array.size`,
// `associative_array.num` and `string.len` as its examples, and rules that
// "When a subroutine built-in method call specifies no arguments, the empty
// parentheses, (), following the subroutine name are optional". The two forms
// of that call are the two cases below.
//
// Until this change this file wrote no method call at all, and no dot. It held
// an unpacked array declaration and two continuous assignments to its
// elements, `assign arr[0] = 8'hAA;` and `assign arr[1] = 8'hBB;`, which is the
// §11.5.2 array addressing
// test/src/unit/test_synthesizer_subclause_11_05_02.cpp covers, and its one
// case asserted the assignment-target report.
//
// Both cases assert a refusal. §5.13's examples are properties of a data type
// rather than storage a netlist can hold, so there is no netlist value for a
// case to read; what there is to assert is that SynthLower::Lower withholds the
// netlist and says why. The source form is the one
// BuiltinMethodSim.ArraySizeWithParens in
// test/src/unit/test_simulator_subclause_05_13.cpp elaborates, written as a
// continuous assignment because SynthLower::Lower passes over an initial
// procedure.

// The call written with the parentheses. Parser::ParseIdentifierPostfixChain
// wraps the member access in a call node when a `(` follows it, so
// SynthLower::LowerExprBit in src/synthesizer/synth_lower.cpp meets
// ExprKind::kCall and NonSynthExprRule in the same file reports it under §13.4.
TEST(BuiltinMethodSynth, ArraySizeCallIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] arr [0:3];\n"
                           "  logic [31:0] s;\n"
                           "  assign s = arr.size();\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a function call has no lowering in the "
                            "synthesizer",
                            4, "13.4"));
}

// The same call written without the parentheses §5.13 makes optional, which is
// a different expression kind and a different report. Nothing wraps the member
// access in a call node, so SynthLower::LowerExprBit meets
// ExprKind::kMemberAccess and NonSynthExprRule answers with the one entry that
// kind carries, which names §7.2.1 and a member of a packed structure. A case
// over the parenthesized form alone would leave the form §5.13 admits untested.
//
// The message this asserts is the wrong name for what the source writes: a
// built-in method call is §5.13, not §7.2.1. Issue #3045 records that defect,
// for the hierarchical name that reaches the same entry, so this case asserts
// what the synthesizer says today rather than what it should say.
TEST(BuiltinMethodSynth, ArraySizeWithoutParenthesesIsReportedUnlowered) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\n"
                           "  logic [7:0] arr [0:2];\n"
                           "  logic [31:0] s;\n"
                           "  assign s = arr.size;\n"
                           "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a member of a packed structure has no lowering in "
                            "the synthesizer",
                            4, "7.2.1"));
}

}  // namespace
