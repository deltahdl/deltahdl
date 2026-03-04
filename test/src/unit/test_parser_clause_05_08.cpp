#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserCh508, TimeLiteral_IntegerNs) {
  auto r = Parse(
      "module m;\n"
      "  initial #40ns;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
}

TEST(ParserA84, PrimaryLiteralTimeLiteral) {
  auto r = Parse("module m; initial #10ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserCh508, TimeLiteral_FixedPointNs) {

  EXPECT_TRUE(ParseOk("module m; initial #2.1ns; endmodule"));
}

TEST(ParserCh508, TimeLiteral_Ps) {
  EXPECT_TRUE(ParseOk("module m; initial #40ps; endmodule"));
}

TEST(ParserCh508, TimeLiteral_Us) {
  EXPECT_TRUE(ParseOk("module m; initial #100us; endmodule"));
}

TEST(ParserA84, TimeLiteralNs) {
  auto r = Parse("module m; initial #5ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserCh508, TimeLiteral_Ms) {
  EXPECT_TRUE(ParseOk("module m; initial #1ms; endmodule"));
}

TEST(ParserCh508, TimeLiteral_Fs) {
  EXPECT_TRUE(ParseOk("module m; initial #500fs; endmodule"));
}

TEST(ParserA84, TimeLiteralUs) {
  auto r = Parse("module m; initial #1us; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA84, TimeLiteralMs) {
  auto r = Parse("module m; initial #2ms; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA84, TimeLiteralS) {
  auto r = Parse("module m; initial #1s; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA223, DelayValueAllTimeLiterals) {
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

TEST(ParserA84, TimeLiteralPs) {
  auto r = Parse("module m; initial #100ps; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA84, TimeLiteralFs) {
  auto r = Parse("module m; initial #50fs; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA84, TimeLiteralFixedPoint) {
  auto r = Parse("module m; initial #1.5ns; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserClause03, Cl3_14_2_2_AllSixUnitsAccepted) {
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

}
