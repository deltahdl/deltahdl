#include "elaborator/sequence_method.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §9.4.4: a level-sensitive wait statement controls execution using the
// built-in sequence method `triggered`, whose definition is shared with
// §16.9.11 and §16.13.6. The wait-statement context is a legal place to apply
// `triggered`, and the method's end-status result is a single bit independent
// of the match's start point.
TEST(SequenceTriggeredElaboration, TriggeredIsLegalInWaitContext) {
  EXPECT_TRUE(IsSequenceMethodContextLegal(
      SequenceMethod::kTriggered, SequenceMethodContext::kWaitStatement,
      /*sequence_treats_formal_as_local_var=*/false));
  EXPECT_TRUE(SequenceMethodResultIsSingleBit());
  EXPECT_FALSE(SequenceMethodResultDependsOnStartPoint());
}

TEST(SequenceTriggeredElaboration, WaitSequenceTriggeredElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    wait(abc.triggered);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequenceTriggeredElaboration, WaitMultipleTriggeredElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c, d;\n"
      "  sequence s1;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  sequence s2;\n"
      "    @(negedge clk) c ##1 d;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    wait(s1.triggered || s2.triggered);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequenceTriggeredElaboration, WaitTriggeredWithActionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, req, ack;\n"
      "  sequence req_ack;\n"
      "    @(posedge clk) req ##[1:5] ack;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    wait(req_ack.triggered);\n"
      "    $display(\"handshake complete\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequenceTriggeredElaboration, WaitTriggeredInForkElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c, d;\n"
      "  sequence s1;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  sequence s2;\n"
      "    @(posedge clk) c ##1 d;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    fork\n"
      "      wait(s1.triggered);\n"
      "      wait(s2.triggered);\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequenceTriggeredElaboration, WaitTriggeredWithDirectBodyElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  sequence ab;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  initial\n"
      "    wait(ab.triggered) $display(\"done\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SequenceTriggeredElaboration, TriggeredCheckAfterWaitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, a, b, c, d;\n"
      "  logic [7:0] which;\n"
      "  sequence s1;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  sequence s2;\n"
      "    @(posedge clk) c ##1 d;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    wait(s1.triggered || s2.triggered);\n"
      "    if (s1.triggered) which = 8'd1;\n"
      "    else if (s2.triggered) which = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
