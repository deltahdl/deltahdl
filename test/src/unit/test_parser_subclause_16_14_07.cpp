#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

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

// §16.14.7: $inferred_clock shall only be used as the default value for a
// formal argument that is untyped or of type event. An `event`-typed formal is
// one of the two permitted forms, so its $inferred_clock default is accepted.
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

// §16.14.7 (negative): a data-typed formal is neither untyped nor of type
// event, so defaulting it to $inferred_clock is illegal and shall be rejected.
TEST(AssertionParsing, InferredClockDefaultOnTypedFormalIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  property p(logic clk_ev = $inferred_clock);\n"
      "    clk_ev |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

// §16.14.7 (negative): a formal declared with the `property` type keyword is
// neither untyped nor of type event, so a $inferred_clock default on it is
// rejected. Exercises the property-type branch of the placement check.
TEST(AssertionParsing, InferredClockDefaultOnPropertyFormalIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  property p(property q = $inferred_clock);\n"
      "    a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

// §16.14.7 (negative): a formal declared with the `sequence` type keyword is
// likewise neither untyped nor of type event, so a $inferred_clock default on
// it is rejected. Exercises the sequence-type branch of the placement check.
TEST(AssertionParsing, InferredClockDefaultOnSequenceFormalIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  property p(sequence s_ev = $inferred_clock);\n"
      "    a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

// §16.14.7: the untyped/event-formal restriction on a $inferred_clock default
// applies in a sequence declaration too. An untyped sequence formal is a
// permitted form, so its $inferred_clock default is accepted.
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

// §16.14.7 (negative): a data-typed sequence formal is neither untyped nor of
// type event, so defaulting it to $inferred_clock is rejected — the same rule
// as for a property formal, observed at the sequence port scanner.
TEST(AssertionParsing, InferredClockDefaultOnTypedSequenceFormalIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  sequence s(logic ev = $inferred_clock);\n"
      "    x ##1 y;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

// §16.14.7 (negative): an inferred clocking or disable function shall be used
// only as the ENTIRE default value expression of a formal. Combining
// $inferred_disable into a larger expression is illegal — observed at the
// property port scanner.
TEST(AssertionParsing, InferredFunctionAsPartialDefaultInPropertyIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  default disable iff rst;\n"
      "  property p(e = $inferred_disable || rst);\n"
      "    a |-> b;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

// §16.14.7 (negative): the same entire-default restriction holds for a sequence
// formal — a $inferred_clock call followed by more of the default expression is
// rejected at the sequence port scanner.
TEST(AssertionParsing, InferredFunctionAsPartialDefaultInSequenceIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  sequence s(e = $inferred_clock ##1 x);\n"
      "    a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
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

}  // namespace
