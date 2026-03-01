// Non-LRM tests

#include "builders_ast.h"
#include "fixture_enum_methods.h"
#include "fixture_evaluator.h"
#include "fixture_lexer.h"
#include "fixture_preprocessor.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// --- §5: Source locations ---
TEST(LexerCh5, SourceLocations) {
  auto tokens = Lex("a\nb c");
  struct Case {
    size_t idx;
    int line;
    int column;
  };
  Case expected[] = {
      {0, 1, 1},
      {1, 2, 1},
      {2, 2, 3},
  };
  for (const auto& c : expected) {
    EXPECT_EQ(tokens[c.idx].loc.line, c.line) << "token " << c.idx;
    EXPECT_EQ(tokens[c.idx].loc.column, c.column) << "token " << c.idx;
  }
}

TEST(LexerCh50603, DollarAloneIsNotSystemIdentifier) {
  // §5.6.3: Grammar requires >= 1 char after $; bare $ is kDollar.
  auto tokens = Lex("$");
  ASSERT_GE(tokens.size(), 2);
  EXPECT_EQ(tokens[0].kind, TokenKind::kDollar);
}

TEST(Preprocessor, DelayToTicks_Basic) {
  TimeScale ts;
  ts.unit = TimeUnit::kNs;
  ts.magnitude = 1;
  // 10 delay units at 1ns with 1ps precision = 10,000 ticks.
  EXPECT_EQ(DelayToTicks(10, ts, TimeUnit::kPs), 10000);
}

// Sim test fixture
// =============================================================================
// A.6.4 Statements — Simulation
// =============================================================================
// ---------------------------------------------------------------------------
// Simulation: statement_or_null and statement execution
// ---------------------------------------------------------------------------
// §12.3: null statement has no effect in simulation
TEST(SimA604, NullStatementNoEffect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    ;\n"
      "    ;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

}  // namespace
