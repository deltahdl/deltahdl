#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// The source of a module whose `always_comb` block copies the four-bit input
// `a` into the output `y` and then runs `stmt`. `stmt` lands on line 4, which
// is the line a report about it stands at.
//
// The block writes the output port itself rather than a variable that a
// continuous assignment then carries to the port, because `SynthLower::Lower`
// lowers `mod->assigns` before `mod->processes`: a port driven by `assign`
// would read the bits the variable held before the block ran, and a test over
// it would be measuring that order rather than the rule it names.
//
// The operand is four bits wide because at width one an increment and a
// decrement build the same netlist, so a one-bit test passes whichever of the
// two the synthesizer built.
std::string AlwaysCombEndingIn(std::string_view stmt) {
  return std::string(
             "module m(input [3:0] a, output logic [3:0] y);\n"
             "  always_comb begin\n"
             "    y = a;\n"
             "    ") +
         std::string(stmt) +
         ";\n"
         "  end\n"
         "endmodule\n";
}

// Drive every value of `a` through the netlist that module lowers to, and
// expect the output to carry `expected(a)`.
//
// `ASSERT_NE(aig, nullptr)` and `EXPECT_FALSE(f.diag.HasErrors())` both hold
// over a graph in which `stmt` never happened, which is how a dropped statement
// went unnoticed, so the sweep is what states that it happened. All sixteen
// values are driven because a single one leaves a netlist computing some other
// function of `a` free to agree at the value chosen.
void ExpectAlwaysCombSweep(std::string_view stmt,
                           uint64_t (*expected)(uint64_t)) {
  SCOPED_TRACE(std::string(stmt));
  SynthFixture f;
  const auto* mod = ElaborateSrc(f, AlwaysCombEndingIn(stmt));
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  const auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  for (uint64_t a = 0; a < 16; ++a) {
    EXPECT_EQ(EvalAigOutputs(*aig, a), expected(a)) << "a = " << a;
  }
}

// §11.4.2 rules that "these increment and decrement assignment operators behave
// as blocking assignments", so `y++` has to leave `a + 1` in the netlist
// exactly as `y = y + 1` would. The test fails on a synthesizer that lowers the
// assignment above the increment and passes the increment over, which leaves
// `y` carrying `a`.
TEST(IncrementSynthesis, PostfixIncrementLowersAsABlockingAssignment) {
  ExpectAlwaysCombSweep("y++", [](uint64_t a) { return (a + 1) & 0xFU; });
}

// §11.4.2 names `++i` and `i++` as one pair of operators, and the two spellings
// reach the synthesizer by different routes: `Parser::ParsePrefixExpr` builds
// `++y` as an `ExprKind::kUnary`, while `MakePostfixUnary` at
// src/parser/expr_parser.cpp:452 builds `y++` as an `ExprKind::kPostfixUnary`.
// A lowering that reads only the postfix kind drops this one and passes the
// test above.
TEST(IncrementSynthesis, PrefixIncrementLowersAsABlockingAssignment) {
  ExpectAlwaysCombSweep("++y", [](uint64_t a) { return (a + 1) & 0xFU; });
}

// §11.4.2 defines `++i`, `--i`, `i++` and `i--` in one sentence and gives the
// four the same behaviour, so the decrements are owed what the increments are.
// A lowering that reaches only the increments passes both tests above while
// `y--` stays dropped. The expected value wraps at the operand's width, so
// decrementing zero leaves fifteen.
TEST(IncrementSynthesis, DecrementLowersAsABlockingAssignment) {
  ExpectAlwaysCombSweep("y--", [](uint64_t a) { return (a - 1) & 0xFU; });
}

// `--y` is the one of the four operators §11.4.2 defines that the three tests
// above leave uncovered: it is spelled as a prefix, so it arrives as an
// `ExprKind::kUnary` like `++y`, and it subtracts, like `y--`. A lowering that
// takes every prefix spelling to be an increment adds one where the source
// subtracts one, and all three tests above pass while it does.
TEST(IncrementSynthesis, PrefixDecrementLowersAsABlockingAssignment) {
  ExpectAlwaysCombSweep("--y", [](uint64_t a) { return (a - 1) & 0xFU; });
}

// §11.4.2 says an increment behaves as a blocking assignment, and this
// synthesizer lowers a blocking assignment only when its target is a whole
// variable: `SynthLower::LowerAssignStmt` returns without touching the graph
// when the left-hand side is not an `ExprKind::kIdentifier`. `y[0]` is an
// `ExprKind::kSelect`, so `y[0]++` is an increment this synthesizer cannot
// build, and what a design writing one is owed is the report rather than a
// netlist the statement never reached.
//
// The report carries no subclause. No rule of IEEE 1800-2023 is broken by
// incrementing a bit-select; what the design meets is a limit of this
// synthesizer, and `Subclause::None()` holds empty text, which is why the
// assertion reads `EXPECT_EQ(d->subclause, "")`. The line is what tells the
// reader which statement is missing, so it is asserted too: a report standing
// at the block or at the module would name the whole design.
TEST(IncrementSynthesis, IncrementOfABitSelectIsReportedRatherThanDropped) {
  SynthFixture f;
  const auto* mod = ElaborateSrc(f, AlwaysCombEndingIn("y[0]++"));
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  const Diagnostic* d = FindDiag(f,
                                 "statement has no lowering in the synthesizer "
                                 "and would be dropped from the netlist");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->subclause, "");
  EXPECT_EQ(d->loc.line, 4u);
}

// The lowering §11.4.2 asks for belongs to the four increment and decrement
// operators and to nothing else an expression statement can hold. `t()` is such
// a statement, and it arrives at `SynthLower::LowerStmt` with nothing said
// about it: `Parser::ParseAssignmentOrExprNoSemi` at
// src/parser/parser_stmt.cpp:793 builds a `StmtKind::kExprStmt` for it,
// `ValidateCombLatchProcess` at src/elaborator/elaborator_process.cpp:303
// leaves it in the process body because `StmtBlocks` answers false for an
// expression statement, and `SynthLower::CheckExprSynthesizable` returns true
// for the `ExprKind::kCall` it holds, which only an `ExprKind::kSystemCall`
// fails.
//
// This synthesizer does not inline a task, so whatever `t` assigns is absent
// from the netlist and the report is what says so. The task declared here has
// an empty body, because no code reads a task body on this path and a body
// would only invite the reader to look for its effect in the graph.
//
// The test fails when `LowerStmt` treats the whole statement kind as the
// increment's business and passes the rest of it over. It is what stops the
// §11.4.2 lowering above from being an amnesty for every expression statement.
TEST(IncrementSynthesis,
     ExpressionStatementWithoutAnIncrementIsReportedRatherThanDropped) {
  SynthFixture f;
  const auto* mod =
      ElaborateSrc(f,
                   "module m(input [3:0] a, output logic [3:0] y);\n"
                   "  task t();\n"
                   "  endtask\n"
                   "  always_comb begin\n"
                   "    y = a;\n"
                   "    t();\n"
                   "  end\n"
                   "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  const Diagnostic* d = FindDiag(f,
                                 "statement has no lowering in the synthesizer "
                                 "and would be dropped from the netlist");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->subclause, "");
  EXPECT_EQ(d->loc.line, 6u);
}

}  // namespace
