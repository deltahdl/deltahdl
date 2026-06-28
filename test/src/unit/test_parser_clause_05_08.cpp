#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TimeLiteralParsing, IntegerNs) {
  auto r = Parse(
      "module m;\n"
      "  initial #40ns;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
}

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
  // 5.8: a time literal "is interpreted as a realtime value scaled to the
  // current time unit." With the module time unit set to us, the literal 2.5us
  // is in that same unit, so it is captured unscaled as 2.5. (Without an
  // explicit timeunit the default unit is ns, which would scale 2.5us to 2500.)
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

}  // namespace
