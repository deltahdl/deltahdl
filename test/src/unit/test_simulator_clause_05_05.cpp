#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

// §5.5 Operators

struct SimCh505Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimCh505Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static uint64_t RunAndGet(const std::string &src, const char *var_name) {
  SimCh505Fixture f;
  auto *design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design)
    return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var)
    return 0;
  return var->value.ToUint64();
}

// ---------------------------------------------------------------------------
// 1. Single-character operator used in expression
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorSingleCharInExpr) {
  // §5.5: Single-character operator (+) used in expression.
  auto result = RunAndGet("module t;\n"
                          "  logic [7:0] result;\n"
                          "  initial result = 8'd10 + 8'd20;\n"
                          "endmodule\n",
                          "result");
  EXPECT_EQ(result, 30u);
}

// ---------------------------------------------------------------------------
// 2. Double-character operator used in expression
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorDoubleCharInExpr) {
  // §5.5: Double-character operator (<<) used in expression.
  auto result = RunAndGet("module t;\n"
                          "  logic [7:0] result;\n"
                          "  initial result = 8'd1 << 3;\n"
                          "endmodule\n",
                          "result");
  EXPECT_EQ(result, 8u);
}

// ---------------------------------------------------------------------------
// 3. Triple-character operator used in expression
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorTripleCharInExpr) {
  // §5.5: Triple-character operator (<<<) — arithmetic left shift.
  auto result = RunAndGet("module t;\n"
                          "  logic [7:0] result;\n"
                          "  initial result = 8'd3 <<< 2;\n"
                          "endmodule\n",
                          "result");
  EXPECT_EQ(result, 12u);
}

// ---------------------------------------------------------------------------
// 4. Unary operator to the left of operand
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorUnaryLeftOfOperand) {
  // §5.5: Unary operators appear to the left of their operand.
  // Unary minus (-) appears to the left of its operand.
  auto result = RunAndGet("module t;\n"
                          "  logic [7:0] result;\n"
                          "  initial result = -8'sd5;\n"
                          "endmodule\n",
                          "result");
  EXPECT_EQ(result & 0xFF, 251u);
}

// ---------------------------------------------------------------------------
// 5. Binary operator between operands
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorBinaryBetweenOperands) {
  // §5.5: Binary operators appear between their operands.
  auto result = RunAndGet("module t;\n"
                          "  logic [7:0] result;\n"
                          "  initial result = 8'd50 - 8'd15;\n"
                          "endmodule\n",
                          "result");
  EXPECT_EQ(result, 35u);
}

// ---------------------------------------------------------------------------
// 6. Conditional operator (two operator characters, three operands)
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorConditionalThreeOperands) {
  // §5.5: Conditional operator has two operator chars separating three
  // operands.
  auto result = RunAndGet("module t;\n"
                          "  logic [7:0] result;\n"
                          "  initial result = 1 ? 8'd42 : 8'd99;\n"
                          "endmodule\n",
                          "result");
  EXPECT_EQ(result, 42u);
}

// ---------------------------------------------------------------------------
// 7. Conditional operator — false branch
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorConditionalFalseBranch) {
  // §5.5: Conditional operator selects third operand when first is false.
  auto result = RunAndGet("module t;\n"
                          "  logic [7:0] result;\n"
                          "  initial result = 0 ? 8'd42 : 8'd99;\n"
                          "endmodule\n",
                          "result");
  EXPECT_EQ(result, 99u);
}

// ---------------------------------------------------------------------------
// 8. Multiple operator types in single expression
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorMixedInExpression) {
  // §5.5: Single- and double-character operators combined.
  auto result = RunAndGet("module t;\n"
                          "  logic [7:0] result;\n"
                          "  initial result = (8'd3 + 8'd5) << 1;\n"
                          "endmodule\n",
                          "result");
  EXPECT_EQ(result, 16u);
}

// ---------------------------------------------------------------------------
// 9. Unary negation operator
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorUnaryNegation) {
  // §5.5: Unary logical negation operator (!) to the left of operand.
  auto result = RunAndGet("module t;\n"
                          "  logic [7:0] result;\n"
                          "  initial result = !1'b0;\n"
                          "endmodule\n",
                          "result");
  EXPECT_EQ(result, 1u);
}

// ---------------------------------------------------------------------------
// 10. Operators without whitespace
// ---------------------------------------------------------------------------
TEST(SimCh505, OperatorNoWhitespace) {
  // §5.5: Operators work as token separators, no whitespace needed.
  auto result = RunAndGet("module t;\n"
                          "  logic [7:0] result;\n"
                          "  initial result=8'd7+8'd3;\n"
                          "endmodule\n",
                          "result");
  EXPECT_EQ(result, 10u);
}
