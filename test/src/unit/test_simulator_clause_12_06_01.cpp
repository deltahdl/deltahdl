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

}  // namespace
