#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, CheckerContextInferenceImplicit) {
  auto* unit = Parse(R"(
    checker check_ctx(logic sig,
        event clock = $inferred_clock);
    endchecker
    module m;
      logic clk, a;
      always @(posedge clk) begin
        check_ctx chk(a);
      end
    endmodule
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST(AssertionParsing, InferredClockInProperty) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  property p_inferred(clk_ev = $inferred_clock);\n"
      "    @clk_ev a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, InferredDisableInProperty) {
  auto r = Parse(
      "module m;\n"
      "  default disable iff rst;\n"
      "  property p_dis(rst_cond = $inferred_disable);\n"
      "    disable iff (rst_cond) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, InferredClockDefaultOnEventFormalIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  property p(event clk_ev = $inferred_clock);\n"
      "    @clk_ev a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, InferredClockDefaultOnTypedFormalIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  property p(logic clk_ev = $inferred_clock);\n"
      "    clk_ev |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "$inferred_clock default requires an untyped or "
                            "event formal argument",
                            3, "16.14.7"));
}

TEST(AssertionParsing, InferredClockDefaultOnPropertyFormalIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  property p(property q = $inferred_clock);\n"
      "    a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "$inferred_clock default requires an untyped or "
                            "event formal argument",
                            3, "16.14.7"));
}

TEST(AssertionParsing, InferredClockDefaultOnSequenceFormalIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  property p(sequence s_ev = $inferred_clock);\n"
      "    a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "$inferred_clock default requires an untyped or "
                            "event formal argument",
                            3, "16.14.7"));
}

TEST(AssertionParsing, InferredClockDefaultOnUntypedSequenceFormalIsAccepted) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  sequence s(ev = $inferred_clock);\n"
      "    x ##1 y;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, InferredClockDefaultOnTypedSequenceFormalIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  sequence s(logic ev = $inferred_clock);\n"
      "    x ##1 y;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "$inferred_clock default requires an untyped or "
                            "event formal argument",
                            3, "16.14.7"));
}

TEST(AssertionParsing, InferredFunctionAsPartialDefaultInPropertyIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  default disable iff rst;\n"
      "  property p(e = $inferred_disable || rst);\n"
      "    a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "an inferred clocking or disable function must be "
                            "the entire default value of a formal argument",
                            3, "16.14.7"));
}

TEST(AssertionParsing, InferredFunctionAsPartialDefaultInSequenceIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  sequence s(e = $inferred_clock ##1 x);\n"
      "    a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "an inferred clocking or disable function must be "
                            "the entire default value of a formal argument",
                            3, "16.14.7"));
}

TEST(AssertionParsing, InferredClockAndDisableTogether) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(negedge clk); endclocking\n"
      "  default disable iff rst;\n"
      "  property p_both(c = $inferred_clock, d = $inferred_disable);\n"
      "    @c disable iff (d) req |-> ack;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, InferredClockDefaultOnACarriedDataTypeIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(shortint d = 3, e = $inferred_clock);\n"
      "    1'b1 ##d 1'b1;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "$inferred_clock default requires an untyped or "
                            "event formal argument",
                            2, "16.14.7"));
}

TEST(AssertionParsing, InferredClockDefaultAfterUntypedOrEventIsAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(shortint d = 3, untyped e = $inferred_clock,\n"
              "             event f = $inferred_clock, g = $inferred_clock);\n"
              "    @(e) 1'b1 ##d 1'b1;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(AssertionParsing, InferredClockDefaultOnAUserDefinedTypeIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [1:0] my_t;\n"
      "  property p(event e, my_t x = $inferred_clock);\n"
      "    @(e) 1'b1;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "$inferred_clock default requires an untyped or "
                            "event formal argument",
                            3, "16.14.7"));
}

void ExpectTypedClockRejected(const std::string& decl) {
  std::string src =
      "module m;\n"
      "  typedef logic [1:0] my_t;\n" +
      decl + "endmodule\n";
  SCOPED_TRACE(src);
  auto r = Parse(src);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "$inferred_clock default requires an untyped or "
                            "event formal argument",
                            3, "16.14.7"));
}

TEST(AssertionParsing,
     InferredClockDefaultOnAnIntOrBitPropertyFormalIsRejected) {
  for (const char* type : {"int", "bit"}) {
    ExpectTypedClockRejected("  property p(" + std::string(type) +
                             " e = $inferred_clock); 1'b1; endproperty\n");
  }
}

TEST(AssertionParsing, InferredClockDefaultOnACarriedPropertyFormalIsRejected) {
  ExpectTypedClockRejected(
      "  property p(logic d, e = $inferred_clock); d; endproperty\n");
}

TEST(AssertionParsing, InferredClockDefaultOnALocalInputFormalIsRejected) {
  ExpectTypedClockRejected(
      "  property p(local input logic e = $inferred_clock); 1'b1; "
      "endproperty\n");
}

TEST(AssertionParsing, InferredClockDefaultOnATypedSequenceFormalIsRejected) {
  for (const char* type : {"int", "my_t", "sequence"}) {
    ExpectTypedClockRejected("  sequence s(" + std::string(type) +
                             " e = $inferred_clock); 1'b1; endsequence\n");
  }
}

TEST(AssertionParsing,
     DISABLED_InferredClockDefaultOnAnImplicitlyTypedFormalIsRejected) {
  for (const char* type : {"[3:0]", "signed"}) {
    ExpectTypedClockRejected("  property p(" + std::string(type) +
                             " e = $inferred_clock); 1'b1; endproperty\n");
    ExpectTypedClockRejected("  sequence s(" + std::string(type) +
                             " e = $inferred_clock); 1'b1; endsequence\n");
  }
}

TEST(AssertionParsing, InferredDisableDefaultOnATypedFormalIsAccepted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p(logic r = $inferred_disable); !r; endproperty\n"
              "  sequence s(bit r = $inferred_disable); !r; endsequence\n"
              "endmodule\n"));
}

}  // namespace
