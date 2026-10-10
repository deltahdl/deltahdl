#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"
#include "helpers_parser_verify.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(TimeLiteralParsing, FixedPointNs) {
  EXPECT_TRUE(ParseOk("module m; initial #2.1ns; endmodule"));
}

TEST(TimeLiteralParsing, AllUnitsInWireDelay) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire #1fs w1;\n"
              "  wire #2ps w2;\n"
              "  wire #3ns w3;\n"
              "  wire #4us w4;\n"
              "  wire #5ms w5;\n"
              "  wire #6s w6;\n"
              "endmodule"));
}

TEST(TimeLiteralParsing, TimeunitAllSixUnits) {
  EXPECT_EQ(ParseTimescale31402("module m; timeunit 1s; endmodule")
                .cu->modules[0]
                ->time_unit,
            TimeUnit::kS);
  EXPECT_EQ(ParseTimescale31402("module m; timeunit 1ms; endmodule")
                .cu->modules[0]
                ->time_unit,
            TimeUnit::kMs);
  EXPECT_EQ(ParseTimescale31402("module m; timeunit 1us; endmodule")
                .cu->modules[0]
                ->time_unit,
            TimeUnit::kUs);
  EXPECT_EQ(ParseTimescale31402("module m; timeunit 1ns; endmodule")
                .cu->modules[0]
                ->time_unit,
            TimeUnit::kNs);
  EXPECT_EQ(ParseTimescale31402("module m; timeunit 1ps; endmodule")
                .cu->modules[0]
                ->time_unit,
            TimeUnit::kPs);
  EXPECT_EQ(ParseTimescale31402("module m; timeunit 1fs; endmodule")
                .cu->modules[0]
                ->time_unit,
            TimeUnit::kFs);
}

TEST(TimeLiteralParsing, TimeLiteralExprKind) {
  auto r = Parse(
      "module m;\n"
      "  initial #10ns;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->kind, StmtKind::kDelay);
  ASSERT_NE(stmt->delay, nullptr);
  EXPECT_EQ(stmt->delay->kind, ExprKind::kTimeLiteral);
}

TEST(TimeLiteralParsing, TimeLiteralRealVal) {
  // 5.8: a time literal reads as a realtime value scaled to the current time
  // unit. With the module time unit set to us, the literal 2.5us is in that
  // same unit, so it is captured unscaled as 2.5. (Without an explicit timeunit
  // the default unit is ns, which would scale 2.5us to 2500.)
  auto r = Parse(
      "module m;\n"
      "  timeunit 1us;\n"
      "  initial #2.5us;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->delay, nullptr);
  EXPECT_DOUBLE_EQ(stmt->delay->real_val, 2.5);
}

TEST(TimeLiteralParsing, TimeLiteralTextIncludesUnit) {
  auto r = Parse(
      "module m;\n"
      "  initial #40ps;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->delay, nullptr);
  EXPECT_EQ(stmt->delay->text, "40ps");
}

// §5.8: the parser records each time literal with its time scope -- a module,
// a package, or neither -- for the elaborator to scale once the `timescale
// before each element is known.
TEST(TimeLiteralParsing, EachLiteralIsRecordedWithItsTimeScope) {
  auto r = Parse(
      "function automatic realtime f(); return 1ns; endfunction\n"
      "package p;\n"
      "  function automatic realtime g(); return 2ns; endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  initial #3ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  const auto& sites = r.cu->time_literals;
  ASSERT_EQ(sites.size(), 3u);
  EXPECT_EQ(sites[0].literal->text, "1ns");
  EXPECT_EQ(sites[0].module, nullptr);
  EXPECT_EQ(sites[0].package, nullptr);
  EXPECT_EQ(sites[1].package, r.cu->packages[0]);
  EXPECT_EQ(sites[1].module, nullptr);
  EXPECT_EQ(sites[2].module, r.cu->modules[0]);
}

// A literal inside a design element goes with the element when one file's
// declarations join another's (AppendCellDeclarations), and one outside every
// element goes with the compilation-unit declarations
// (AppendCompilationUnitDeclarations), so a unit read back alone keeps its own.
TEST(TimeLiteralParsing, LiteralsTravelWithTheirDeclarations) {
  Expr in_module;
  Expr in_package;
  Expr in_unit;
  ModuleDecl mod;
  PackageDecl pkg;
  CompilationUnit src;
  src.time_literals = {{&in_module, &mod, nullptr},
                       {&in_unit, nullptr, nullptr},
                       {&in_package, nullptr, &pkg}};
  CompilationUnit cells;
  AppendCellDeclarations(cells, src);
  ASSERT_EQ(cells.time_literals.size(), 2u);
  EXPECT_EQ(cells.time_literals[0].literal, &in_module);
  EXPECT_EQ(cells.time_literals[1].literal, &in_package);
  CompilationUnit scope;
  AppendCompilationUnitDeclarations(scope, src);
  ASSERT_EQ(scope.time_literals.size(), 1u);
  EXPECT_EQ(scope.time_literals[0].literal, &in_unit);
}

}  // namespace
