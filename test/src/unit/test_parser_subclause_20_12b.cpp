#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(GlobalClockingArguments, OneExpressionIsAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $past_gclk(a));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $rose_gclk(a));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $fell_gclk(a));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $stable_gclk(a));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $changed_gclk(a));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $future_gclk(a));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $rising_gclk(a));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $falling_gclk(a));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $steady_gclk(a));\n"
              "endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, g, clk, x;\n"
              "  assert property (@(posedge clk) $changing_gclk(a));\n"
              "endmodule\n"));
}

TEST(GlobalClockingArguments, DISABLED_PastGclkWithNoArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $past_gclk());\n"
            "endmodule\n")
          .diags,
      "$past_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $past_gclk();\n"
                                  "endmodule\n")
                                .diags,
                            "$past_gclk takes exactly one expression argument",
                            3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_PastGclkWithASecondExpressionIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $past_gclk(a, b));\n"
            "endmodule\n")
          .diags,
      "$past_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $past_gclk(a, b);\n"
                                  "endmodule\n")
                                .diags,
                            "$past_gclk takes exactly one expression argument",
                            3, "20.12"));
}

TEST(GlobalClockingArguments, DISABLED_PastGclkWithAClockingEventIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $past_gclk(a, @clk));\n"
            "endmodule\n")
          .diags,
      "$past_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $past_gclk(a, @clk);\n"
                                  "endmodule\n")
                                .diags,
                            "$past_gclk takes exactly one expression argument",
                            3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_PastGclkWithAnEmptyTrailingSlotIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $past_gclk(a,));\n"
            "endmodule\n")
          .diags,
      "$past_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $past_gclk(a,);\n"
                                  "endmodule\n")
                                .diags,
                            "$past_gclk takes exactly one expression argument",
                            3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_PastGclkWithADataTypeArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $past_gclk(int));\n"
            "endmodule\n")
          .diags,
      "$past_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $past_gclk(int);\n"
                                  "endmodule\n")
                                .diags,
                            "$past_gclk takes exactly one expression argument",
                            3, "20.12"));
}

TEST(GlobalClockingArguments, DISABLED_RoseGclkWithNoArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $rose_gclk());\n"
            "endmodule\n")
          .diags,
      "$rose_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $rose_gclk();\n"
                                  "endmodule\n")
                                .diags,
                            "$rose_gclk takes exactly one expression argument",
                            3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_RoseGclkWithASecondExpressionIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $rose_gclk(a, b));\n"
            "endmodule\n")
          .diags,
      "$rose_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $rose_gclk(a, b);\n"
                                  "endmodule\n")
                                .diags,
                            "$rose_gclk takes exactly one expression argument",
                            3, "20.12"));
}

TEST(GlobalClockingArguments, DISABLED_RoseGclkWithAClockingEventIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $rose_gclk(a, @clk));\n"
            "endmodule\n")
          .diags,
      "$rose_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $rose_gclk(a, @clk);\n"
                                  "endmodule\n")
                                .diags,
                            "$rose_gclk takes exactly one expression argument",
                            3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_RoseGclkWithAnEmptyTrailingSlotIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $rose_gclk(a,));\n"
            "endmodule\n")
          .diags,
      "$rose_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $rose_gclk(a,);\n"
                                  "endmodule\n")
                                .diags,
                            "$rose_gclk takes exactly one expression argument",
                            3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_RoseGclkWithADataTypeArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $rose_gclk(int));\n"
            "endmodule\n")
          .diags,
      "$rose_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $rose_gclk(int);\n"
                                  "endmodule\n")
                                .diags,
                            "$rose_gclk takes exactly one expression argument",
                            3, "20.12"));
}

TEST(GlobalClockingArguments, DISABLED_FellGclkWithNoArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $fell_gclk());\n"
            "endmodule\n")
          .diags,
      "$fell_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $fell_gclk();\n"
                                  "endmodule\n")
                                .diags,
                            "$fell_gclk takes exactly one expression argument",
                            3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_FellGclkWithASecondExpressionIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $fell_gclk(a, b));\n"
            "endmodule\n")
          .diags,
      "$fell_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $fell_gclk(a, b);\n"
                                  "endmodule\n")
                                .diags,
                            "$fell_gclk takes exactly one expression argument",
                            3, "20.12"));
}

TEST(GlobalClockingArguments, DISABLED_FellGclkWithAClockingEventIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $fell_gclk(a, @clk));\n"
            "endmodule\n")
          .diags,
      "$fell_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $fell_gclk(a, @clk);\n"
                                  "endmodule\n")
                                .diags,
                            "$fell_gclk takes exactly one expression argument",
                            3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_FellGclkWithAnEmptyTrailingSlotIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $fell_gclk(a,));\n"
            "endmodule\n")
          .diags,
      "$fell_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $fell_gclk(a,);\n"
                                  "endmodule\n")
                                .diags,
                            "$fell_gclk takes exactly one expression argument",
                            3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_FellGclkWithADataTypeArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $fell_gclk(int));\n"
            "endmodule\n")
          .diags,
      "$fell_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(Parse("module m;\n"
                                  "  logic a, b, g, clk, x;\n"
                                  "  initial x = $fell_gclk(int);\n"
                                  "endmodule\n")
                                .diags,
                            "$fell_gclk takes exactly one expression argument",
                            3, "20.12"));
}

TEST(GlobalClockingArguments, DISABLED_StableGclkWithNoArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $stable_gclk());\n"
            "endmodule\n")
          .diags,
      "$stable_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $stable_gclk();\n"
            "endmodule\n")
          .diags,
      "$stable_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_StableGclkWithASecondExpressionIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $stable_gclk(a, b));\n"
            "endmodule\n")
          .diags,
      "$stable_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $stable_gclk(a, b);\n"
            "endmodule\n")
          .diags,
      "$stable_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments, DISABLED_StableGclkWithAClockingEventIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $stable_gclk(a, @clk));\n"
            "endmodule\n")
          .diags,
      "$stable_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $stable_gclk(a, @clk);\n"
            "endmodule\n")
          .diags,
      "$stable_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_StableGclkWithAnEmptyTrailingSlotIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $stable_gclk(a,));\n"
            "endmodule\n")
          .diags,
      "$stable_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $stable_gclk(a,);\n"
            "endmodule\n")
          .diags,
      "$stable_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_StableGclkWithADataTypeArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $stable_gclk(int));\n"
            "endmodule\n")
          .diags,
      "$stable_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $stable_gclk(int);\n"
            "endmodule\n")
          .diags,
      "$stable_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments, DISABLED_ChangedGclkWithNoArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $changed_gclk());\n"
            "endmodule\n")
          .diags,
      "$changed_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $changed_gclk();\n"
            "endmodule\n")
          .diags,
      "$changed_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_ChangedGclkWithASecondExpressionIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $changed_gclk(a, b));\n"
            "endmodule\n")
          .diags,
      "$changed_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $changed_gclk(a, b);\n"
            "endmodule\n")
          .diags,
      "$changed_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_ChangedGclkWithAClockingEventIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $changed_gclk(a, @clk));\n"
            "endmodule\n")
          .diags,
      "$changed_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $changed_gclk(a, @clk);\n"
            "endmodule\n")
          .diags,
      "$changed_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_ChangedGclkWithAnEmptyTrailingSlotIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $changed_gclk(a,));\n"
            "endmodule\n")
          .diags,
      "$changed_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $changed_gclk(a,);\n"
            "endmodule\n")
          .diags,
      "$changed_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_ChangedGclkWithADataTypeArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $changed_gclk(int));\n"
            "endmodule\n")
          .diags,
      "$changed_gclk takes exactly one expression argument", 3, "20.12"));
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  initial x = $changed_gclk(int);\n"
            "endmodule\n")
          .diags,
      "$changed_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments, DISABLED_FutureGclkWithNoArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $future_gclk());\n"
            "endmodule\n")
          .diags,
      "$future_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_FutureGclkWithASecondExpressionIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $future_gclk(a, b));\n"
            "endmodule\n")
          .diags,
      "$future_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments, DISABLED_FutureGclkWithAClockingEventIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $future_gclk(a, @clk));\n"
            "endmodule\n")
          .diags,
      "$future_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_FutureGclkWithAnEmptyTrailingSlotIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $future_gclk(a,));\n"
            "endmodule\n")
          .diags,
      "$future_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_FutureGclkWithADataTypeArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $future_gclk(int));\n"
            "endmodule\n")
          .diags,
      "$future_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments, DISABLED_RisingGclkWithNoArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $rising_gclk());\n"
            "endmodule\n")
          .diags,
      "$rising_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_RisingGclkWithASecondExpressionIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $rising_gclk(a, b));\n"
            "endmodule\n")
          .diags,
      "$rising_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments, DISABLED_RisingGclkWithAClockingEventIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $rising_gclk(a, @clk));\n"
            "endmodule\n")
          .diags,
      "$rising_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_RisingGclkWithAnEmptyTrailingSlotIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $rising_gclk(a,));\n"
            "endmodule\n")
          .diags,
      "$rising_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_RisingGclkWithADataTypeArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $rising_gclk(int));\n"
            "endmodule\n")
          .diags,
      "$rising_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments, DISABLED_FallingGclkWithNoArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $falling_gclk());\n"
            "endmodule\n")
          .diags,
      "$falling_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_FallingGclkWithASecondExpressionIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $falling_gclk(a, b));\n"
            "endmodule\n")
          .diags,
      "$falling_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_FallingGclkWithAClockingEventIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $falling_gclk(a, @clk));\n"
            "endmodule\n")
          .diags,
      "$falling_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_FallingGclkWithAnEmptyTrailingSlotIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $falling_gclk(a,));\n"
            "endmodule\n")
          .diags,
      "$falling_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_FallingGclkWithADataTypeArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $falling_gclk(int));\n"
            "endmodule\n")
          .diags,
      "$falling_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments, DISABLED_SteadyGclkWithNoArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $steady_gclk());\n"
            "endmodule\n")
          .diags,
      "$steady_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_SteadyGclkWithASecondExpressionIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $steady_gclk(a, b));\n"
            "endmodule\n")
          .diags,
      "$steady_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments, DISABLED_SteadyGclkWithAClockingEventIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $steady_gclk(a, @clk));\n"
            "endmodule\n")
          .diags,
      "$steady_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_SteadyGclkWithAnEmptyTrailingSlotIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $steady_gclk(a,));\n"
            "endmodule\n")
          .diags,
      "$steady_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_SteadyGclkWithADataTypeArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $steady_gclk(int));\n"
            "endmodule\n")
          .diags,
      "$steady_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments, DISABLED_ChangingGclkWithNoArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $changing_gclk());\n"
            "endmodule\n")
          .diags,
      "$changing_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_ChangingGclkWithASecondExpressionIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $changing_gclk(a, b));\n"
            "endmodule\n")
          .diags,
      "$changing_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_ChangingGclkWithAClockingEventIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $changing_gclk(a, @clk));\n"
            "endmodule\n")
          .diags,
      "$changing_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_ChangingGclkWithAnEmptyTrailingSlotIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $changing_gclk(a,));\n"
            "endmodule\n")
          .diags,
      "$changing_gclk takes exactly one expression argument", 3, "20.12"));
}

TEST(GlobalClockingArguments,
     DISABLED_ChangingGclkWithADataTypeArgumentIsReported) {
  EXPECT_TRUE(ReportedError(
      Parse("module m;\n"
            "  logic a, b, g, clk, x;\n"
            "  assert property (@(posedge clk) $changing_gclk(int));\n"
            "endmodule\n")
          .diags,
      "$changing_gclk takes exactly one expression argument", 3, "20.12"));
}

}  // namespace
