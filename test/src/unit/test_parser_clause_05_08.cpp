#include "fixture_parser.h"
#include "fixture_preprocessor_timescale.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, IntegerNs) {
  auto r = Parse(
      "module m;\n"
      "  initial #40ns;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
}

TEST(LexicalConventionParsing, FixedPointNs) {
  EXPECT_TRUE(ParseOk("module m; initial #2.1ns; endmodule"));
}

TEST(LexicalConventionParsing, Ps) {
  EXPECT_TRUE(ParseOk("module m; initial #40ps; endmodule"));
}

TEST(LexicalConventionParsing, Us) {
  EXPECT_TRUE(ParseOk("module m; initial #100us; endmodule"));
}

TEST(LexicalConventionParsing, Ms) {
  EXPECT_TRUE(ParseOk("module m; initial #1ms; endmodule"));
}

TEST(LexicalConventionParsing, Fs) {
  EXPECT_TRUE(ParseOk("module m; initial #500fs; endmodule"));
}

TEST(LexicalConventionParsing, S) {
  EXPECT_TRUE(ParseOk("module m; initial #1s; endmodule"));
}

TEST(LexicalConventionParsing, FixedPointUs) {
  EXPECT_TRUE(ParseOk("module m; initial #1.5ns; endmodule"));
}

TEST(LexicalConventionParsing, AllUnitsInWireDelay) {
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

TEST(LexicalConventionParsing, TimeunitAllSixUnits) {
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

}  // namespace
