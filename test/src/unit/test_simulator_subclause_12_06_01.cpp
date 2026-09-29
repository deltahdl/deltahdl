#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(CaseMatchesItemSim, CaseMatchesConstantMatch) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd2;\n"
                      "    case(sel) matches\n"
                      "      8'd1: x = 8'd10;\n"
                      "      8'd2: x = 8'd20;\n"
                      "      8'd3: x = 8'd30;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            20u);
}

TEST(CaseMatchesItemSim, CaseMatchesDefaultFallthrough) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd99;\n"
                      "    case(sel) matches\n"
                      "      8'd1: x = 8'd10;\n"
                      "      8'd2: x = 8'd20;\n"
                      "      default: x = 8'd77;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            77u);
}

TEST(CaseMatchesItemSim, CaseMatchesFirstMatchWins) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd1;\n"
                      "    case(sel) matches\n"
                      "      8'd1: x = 8'd10;\n"
                      "      8'd1: x = 8'd20;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            10u);
}

TEST(CaseMatchesItemSim, CaseMatchesGuardTrue) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  logic en;\n"
                      "  initial begin\n"
                      "    sel = 8'd5;\n"
                      "    en = 1'b1;\n"
                      "    case(sel) matches\n"
                      "      8'd5 &&& en: x = 8'd10;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            10u);
}

TEST(CaseMatchesItemSim, CaseMatchesGuardFalse) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  logic en;\n"
                      "  initial begin\n"
                      "    sel = 8'd5;\n"
                      "    en = 1'b0;\n"
                      "    case(sel) matches\n"
                      "      8'd5 &&& en: x = 8'd10;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            99u);
}

TEST(CaseMatchesItemSim, CaseMatchesGuardFalseSecondMatches) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd5;\n"
                      "    case(sel) matches\n"
                      "      8'd5 &&& 1'b0: x = 8'd10;\n"
                      "      8'd5: x = 8'd20;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            20u);
}

TEST(CaseMatchesItemSim, CasezMatchesWildcard) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [3:0] sel;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    sel = 4'b1010;\n"
                      "    casez(sel) matches\n"
                      "      4'b1???: x = 8'd1;\n"
                      "      4'b0???: x = 8'd2;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            1u);
}

TEST(CaseMatchesItemSim, PriorityCaseMatchesNoMatchViolation) {
  SimFixture f;
  RunModuleNoVar(f,
                 "module t;\n"
                 "  logic [7:0] sel, x;\n"
                 "  initial begin\n"
                 "    sel = 8'd99;\n"
                 "    x = 8'd0;\n"
                 "    priority case(sel) matches\n"
                 "      8'd1: x = 8'd10;\n"
                 "      8'd2: x = 8'd20;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §12.6.1: `priority` implies some case item shall be selected, but a default
// item counts as that selection. So a priority pattern-matching case that
// matches no explicit item yet supplies a default runs the default with no
// violation — the priority no-match check is reached only when no default
// exists. This is the negative twin of PriorityCaseMatchesNoMatchViolation.
TEST(CaseMatchesItemSim, PriorityCaseMatchesNoMatchWithDefaultNoViolation) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd99;\n"
                      "    priority case(sel) matches\n"
                      "      8'd1: x = 8'd10;\n"
                      "      8'd2: x = 8'd20;\n"
                      "      default: x = 8'd55;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            55u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(CaseMatchesItemSim, UniqueCaseMatchesOverlapViolation) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd1;\n"
                      "    unique case(sel) matches\n"
                      "      8'd1: x = 8'd10;\n"
                      "      8'd1: x = 8'd20;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            10u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(CaseMatchesItemSim, CaseMatchesNoMatchNoDefault) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd99;\n"
                      "    x = 8'd42;\n"
                      "    case(sel) matches\n"
                      "      8'd1: x = 8'd10;\n"
                      "      8'd2: x = 8'd20;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            42u);
}

TEST(CaseMatchesItemSim, CaseMatchesWildcardPattern) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [3:0] sel;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    sel = 4'b1010;\n"
                      "    case(sel) matches\n"
                      "      4'b0???: x = 8'd1;\n"
                      "      4'b1???: x = 8'd2;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            2u);
}

TEST(CaseMatchesItemSim, CaseMatchesWildcardNoMatch) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [3:0] sel;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    sel = 4'b1010;\n"
                      "    case(sel) matches\n"
                      "      4'b0??0: x = 8'd1;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            99u);
}

TEST(CaseMatchesItemSim, CasexMatchesXInSelectorDontCare) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [3:0] sel;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    sel = 4'bx010;\n"
                      "    casex(sel) matches\n"
                      "      4'b1010: x = 8'd1;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            1u);
}

TEST(CaseMatchesItemSim, CaseMatchesXInSelectorNoMatch) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [3:0] sel;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    sel = 4'bx010;\n"
                      "    case(sel) matches\n"
                      "      4'b1010: x = 8'd1;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            99u);
}

TEST(CaseMatchesItemSim, CaseMatchesCommaSeparatedPatterns) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd3;\n"
                      "    case(sel) matches\n"
                      "      8'd1, 8'd2, 8'd3: x = 8'd10;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            10u);
}

// §12.6.1: the expression in parentheses of a pattern-matching case statement
// shall be evaluated exactly once. A side-effecting function supplies the
// selector; its counter must read 1 after the whole case statement runs.
TEST(CaseMatchesItemSim, CaseMatchesSelectorEvaluatedExactlyOnce) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  int cnt;\n"
                      "  logic [7:0] x;\n"
                      "  function automatic logic [7:0] sel_fn();\n"
                      "    cnt = cnt + 1;\n"
                      "    return 8'd2;\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    cnt = 0;\n"
                      "    x = 8'd0;\n"
                      "    case (sel_fn()) matches\n"
                      "      8'd1: x = 8'd11;\n"
                      "      8'd2: x = 8'd22;\n"
                      "      8'd3: x = 8'd33;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "cnt"),
            1u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 22u);
}

TEST(CaseMatchesItemSim, CaseMatchesCommaSeparatedNoneMatch) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd5;\n"
                      "    case(sel) matches\n"
                      "      8'd1, 8'd2, 8'd3: x = 8'd10;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            99u);
}

// §12.6.1: during the linear search the default item is ignored; it is only
// reached as a fallback when no item is selected. Here the default appears
// first textually but a later item still matches, so the later item runs.
TEST(CaseMatchesItemSim, CaseMatchesDefaultIgnoredDuringSearch) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd2;\n"
                      "    case(sel) matches\n"
                      "      default: x = 8'd99;\n"
                      "      8'd1: x = 8'd10;\n"
                      "      8'd2: x = 8'd20;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            20u);
}

// §12.6.1: items are tested in the exact order given, so when two distinct
// patterns both match, the earliest one in the list is selected.
TEST(CaseMatchesItemSim, CaseMatchesFirstOfOverlappingPatternsWins) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [3:0] sel;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    sel = 4'b1010;\n"
                      "    casez(sel) matches\n"
                      "      4'b1???: x = 8'd1;\n"
                      "      4'b1010: x = 8'd2;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            1u);
}

// §12.6.1: a `unique` pattern-matching case implies not only that at most one
// item is selected but also that *some* item shall be selected. With no item
// matching the selector and no default present, that "some item" requirement is
// violated, so the unique check reports a violation. This is the other half of
// unique's meaning from the already-covered overlap case.
TEST(CaseMatchesItemSim, UniqueCaseMatchesNoMatchViolation) {
  SimFixture f;
  RunModuleNoVar(f,
                 "module t;\n"
                 "  logic [7:0] sel, x;\n"
                 "  initial begin\n"
                 "    sel = 8'd99;\n"
                 "    x = 8'd0;\n"
                 "    unique case(sel) matches\n"
                 "      8'd1: x = 8'd10;\n"
                 "      8'd2: x = 8'd20;\n"
                 "    endcase\n"
                 "  end\n"
                 "endmodule\n");
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// §12.6.1: the "some item shall be selected" requirement of `unique` is
// satisfied by a default item, so a unique pattern-matching case that matches
// no explicit item but has a default runs the default without a violation.
TEST(CaseMatchesItemSim, UniqueCaseMatchesNoMatchWithDefaultNoViolation) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd99;\n"
                      "    unique case(sel) matches\n"
                      "      8'd1: x = 8'd10;\n"
                      "      8'd2: x = 8'd20;\n"
                      "      default: x = 8'd77;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            77u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

// §12.6.1: an item is selected only when the filter evaluates to a determined
// value other than 0. An x-valued filter is not determined, so even though the
// pattern matches, the item is not selected and the default runs instead.
TEST(CaseMatchesItemSim, CaseMatchesGuardUnknownNotSelected) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  logic en;\n"
                      "  initial begin\n"
                      "    sel = 8'd5;\n"
                      "    en = 1'bx;\n"
                      "    case(sel) matches\n"
                      "      8'd5 &&& en: x = 8'd10;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            99u);
}

// §12.6.1: a case-item left-hand side may be a constant-expression pattern, and
// V is matched against it. The constant value can come from a parameter, which
// takes a different evaluation path than an inline literal. Built from real
// §11.2.1 parameter syntax and run: the selector equals the parameter's value,
// so that item is selected. If the parameter resolved to 0 the default (x=0)
// would run instead, so x==20 proves the parameter's value drove the match.
TEST(CaseMatchesItemSim, CaseMatchesParameterPattern) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  parameter P = 8'd2;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd2;\n"
                      "    case(sel) matches\n"
                      "      P: x = 8'd20;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            20u);
}

// §12.6.1: same rule as above, but the constant-expression pattern is produced
// by a localparam. localparam resolution is a distinct path from a parameter or
// a literal; x==70 confirms the localparam's value was matched against V.
TEST(CaseMatchesItemSim, CaseMatchesLocalparamPattern) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  localparam LP = 8'd7;\n"
                      "  logic [7:0] sel, x;\n"
                      "  initial begin\n"
                      "    sel = 8'd7;\n"
                      "    case(sel) matches\n"
                      "      LP: x = 8'd70;\n"
                      "      default: x = 8'd0;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            70u);
}

// §12.6.1: the Boolean filter selects the item when it is a determined value
// other than 0 — not only the single bit 1. Here the filter is a multi-bit
// value (9), which is determined and non-zero, so the guarded item is selected.
TEST(CaseMatchesItemSim, CaseMatchesGuardMultibitNonzeroTrue) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [7:0] sel, x;\n"
                      "  logic [3:0] fexpr;\n"
                      "  initial begin\n"
                      "    sel = 8'd5;\n"
                      "    fexpr = 4'd9;\n"
                      "    case(sel) matches\n"
                      "      8'd5 &&& fexpr: x = 8'd10;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            10u);
}

// §12.6.1: casez pattern matching ignores z bits wherever two bits are
// compared, including z bits on the selector side. Bit 3 of the selector is z,
// so it is treated as a don't-care while the remaining bits equal the pattern,
// giving a match. Complements CasezMatchesWildcard, which places the z bits in
// the pattern.
TEST(CaseMatchesItemSim, CasezMatchesZInSelectorIgnored) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [3:0] sel;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    sel = 4'bz010;\n"
                      "    casez(sel) matches\n"
                      "      4'b1010: x = 8'd1;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            1u);
}

// §12.6.1: the casex form ignores both z and x bits during pattern matching.
// CasexMatchesXInSelectorDontCare covers the x case; here the selector's high
// bit is z, and casex still treats it as a don't-care so the item matches.
TEST(CaseMatchesItemSim, CasexMatchesZInSelectorIgnored) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      "module t;\n"
                      "  logic [3:0] sel;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    sel = 4'bz010;\n"
                      "    casex(sel) matches\n"
                      "      4'b1010: x = 8'd1;\n"
                      "      default: x = 8'd99;\n"
                      "    endcase\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            1u);
}

// A module declaring the two tagged unions the pattern tests below match
// against: `VInt` with a void and an int member, and `U` with two four-bit
// members, so a member value can be the same under either tag.
constexpr const char* kTaggedTypes =
    "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
    "  typedef union tagged { logic [3:0] A; logic [3:0] B; } U;\n";

std::string TaggedModule(const std::string& body) {
  return "module t;\n" + std::string(kTaggedTypes) + body + "endmodule\n";
}

// §12.6: `tagged Valid .n` matches a value tagged Valid and binds `n` to its
// member, which the item's statement reads (§12.6.1's Example 1).
TEST(CaseMatchesItemSim, AnIdentifierMemberPatternBindsTheMember) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      TaggedModule("  VInt v;\n"
                                   "  int y;\n"
                                   "  initial begin\n"
                                   "    v = tagged Valid (37);\n"
                                   "    case (v) matches\n"
                                   "      tagged Invalid : y = 1;\n"
                                   "      tagged Valid .n : y = n;\n"
                                   "    endcase\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            37u);
}

// §12.6: a tagged pattern matches only a value carrying its tag, so
// `tagged Valid .n` does not match a value tagged Invalid.
TEST(CaseMatchesItemSim, ATaggedPatternRejectsAValueOfAnotherTag) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      TaggedModule("  VInt v;\n"
                                   "  int y;\n"
                                   "  initial begin\n"
                                   "    v = tagged Invalid;\n"
                                   "    case (v) matches\n"
                                   "      tagged Valid .n : y = 1;\n"
                                   "      default : y = 2;\n"
                                   "    endcase\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            2u);
}

// §12.6: the wildcard `.*` under a tag matches any member of that tag.
TEST(CaseMatchesItemSim, AWildcardMemberPatternMatchesItsTag) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      TaggedModule("  VInt v;\n"
                                   "  int y;\n"
                                   "  initial begin\n"
                                   "    v = tagged Valid (12);\n"
                                   "    case (v) matches\n"
                                   "      tagged Valid .* : y = 1;\n"
                                   "      default : y = 2;\n"
                                   "    endcase\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            1u);
}

// §12.6: a constant member pattern is compared only under its own tag, so
// `tagged A 6` does not select a value tagged B whose member is also 6.
TEST(CaseMatchesItemSim, AConstantMemberPatternComparesTheTagFirst) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      TaggedModule("  U u;\n"
                                   "  int y;\n"
                                   "  initial begin\n"
                                   "    u = tagged B (4'd6);\n"
                                   "    case (u) matches\n"
                                   "      tagged A 6 : y = 1;\n"
                                   "      tagged B 6 : y = 2;\n"
                                   "      default : y = 3;\n"
                                   "    endcase\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            2u);
}

// §12.6.1: casez ignores a z bit wherever two bits are compared during the
// match, member bits included, so the member 4'b1z01 matches 4'b1101.
TEST(CaseMatchesItemSim, CasezIgnoresAZBitOfTheMember) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      TaggedModule("  U u;\n"
                                   "  int y;\n"
                                   "  initial begin\n"
                                   "    u = tagged B (4'b1z01);\n"
                                   "    casez (u) matches\n"
                                   "      tagged B 4'b1101 : y = 1;\n"
                                   "      default : y = 2;\n"
                                   "    endcase\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            1u);
}

// §12.6.1: the identifiers a pattern binds are in scope in the item's `&&&`
// filter. A(3) passes `x < 8` and takes the first item; A(9) fails it and
// falls to the second.
TEST(CaseMatchesItemSim, TheFilterReadsTheBoundIdentifier) {
  SimFixture f;
  auto* design =
      ElaborateSrc(TaggedModule("  U u;\n"
                                "  int y, z;\n"
                                "  initial begin\n"
                                "    u = tagged A (4'd3);\n"
                                "    case (u) matches\n"
                                "      tagged A .x &&& (x < 8) : y = x + 100;\n"
                                "      tagged A .x : y = 1;\n"
                                "    endcase\n"
                                "    u = tagged A (4'd9);\n"
                                "    case (u) matches\n"
                                "      tagged A .x &&& (x < 8) : z = x + 100;\n"
                                "      tagged A .x : z = 1;\n"
                                "    endcase\n"
                                "  end\n"),
                   f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindVariable("y");
  auto* z = f.ctx.FindVariable("z");
  ASSERT_NE(y, nullptr);
  ASSERT_NE(z, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 103u);
  EXPECT_EQ(z->value.ToUint64(), 1u);
}

// A module declaring the structure and the tagged union of structures the
// structure-pattern tests below match against.
std::string StructModule(const std::string& body) {
  return "module t;\n"
         "  typedef struct { bit [3:0] a; bit [3:0] b; } S;\n"
         "  typedef union tagged {\n"
         "    struct { bit [4:0] reg1, reg2, regd; } Add;\n"
         "    struct { bit [1:0] cc; bit [9:0] addr; } JmpC;\n"
         "  } Instr;\n" +
         body + "endmodule\n";
}

// §12.6: a positional structure pattern of constants matches a structure
// whose members equal them in declaration order.
TEST(CaseMatchesItemSim, APositionalStructurePatternMatchesEachMember) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      StructModule("  S s;\n"
                                   "  int y;\n"
                                   "  initial begin\n"
                                   "    s = '{5, 9};\n"
                                   "    case (s) matches\n"
                                   "      '{9, 5} : y = 1;\n"
                                   "      '{5, 9} : y = 2;\n"
                                   "      default : y = 3;\n"
                                   "    endcase\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            2u);
}

// §12.6: a wildcard element of a structure pattern matches any member, and
// the rest still has to match.
TEST(CaseMatchesItemSim, AStructurePatternWildcardMatchesAnyMember) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      StructModule("  S s;\n"
                                   "  int y;\n"
                                   "  initial begin\n"
                                   "    s = '{5, 9};\n"
                                   "    case (s) matches\n"
                                   "      '{.*, 8} : y = 1;\n"
                                   "      '{.*, 9} : y = 2;\n"
                                   "      default : y = 3;\n"
                                   "    endcase\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            2u);
}

// §12.6: a named structure pattern matches the member each name names and
// binds an identifier to the member it stands for.
TEST(CaseMatchesItemSim, ANamedStructurePatternBindsAMember) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      StructModule("  S s;\n"
                                   "  int y;\n"
                                   "  initial begin\n"
                                   "    s = '{5, 9};\n"
                                   "    case (s) matches\n"
                                   "      '{b:5, a:.aa} : y = 1;\n"
                                   "      '{a:5, b:.bb} : y = bb + 100;\n"
                                   "      default : y = 3;\n"
                                   "    endcase\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            109u);
}

// §12.6.1's Example 6: a named structure pattern under a tag, its members in
// an order of its own and one of them left out.
TEST(CaseMatchesItemSim, ANamedStructurePatternUnderATagBindsItsMembers) {
  SimFixture f;
  auto* design = ElaborateSrc(
      StructModule("  Instr instr;\n"
                   "  int y, z;\n"
                   "  initial begin\n"
                   "    instr = tagged Add '{1, 2, 6};\n"
                   "    case (instr) matches\n"
                   "      tagged Add '{reg2:.r2, regd:.rd, reg1:.r1} :\n"
                   "        y = r1 * 100 + r2 * 10 + rd;\n"
                   "      tagged JmpC '{addr:.a} : y = a;\n"
                   "    endcase\n"
                   "    instr = tagged JmpC '{2, 300};\n"
                   "    case (instr) matches\n"
                   "      tagged Add '{reg2:.r2, regd:.rd, reg1:.r1} :\n"
                   "        z = r1 * 100 + r2 * 10 + rd;\n"
                   "      tagged JmpC '{addr:.a} : z = a;\n"
                   "    endcase\n"
                   "  end\n"),
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindVariable("y");
  auto* z = f.ctx.FindVariable("z");
  ASSERT_NE(y, nullptr);
  ASSERT_NE(z, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 126u);
  EXPECT_EQ(z->value.ToUint64(), 300u);
}

// §13.4: a function body selects the item and binds its identifiers as a
// process does.
TEST(CaseMatchesItemSim, AFunctionBodyBindsTheMatchedMember) {
  SimFixture f;
  EXPECT_EQ(RunModule(f,
                      TaggedModule("  VInt v;\n"
                                   "  int y;\n"
                                   "  function int f();\n"
                                   "    case (v) matches\n"
                                   "      tagged Invalid : return 1;\n"
                                   "      tagged Valid .n : return n;\n"
                                   "    endcase\n"
                                   "    return 2;\n"
                                   "  endfunction\n"
                                   "  initial begin\n"
                                   "    v = tagged Valid (37);\n"
                                   "    y = f();\n"
                                   "  end\n")
                          .c_str(),
                      "y"),
            37u);
}

}  // namespace
