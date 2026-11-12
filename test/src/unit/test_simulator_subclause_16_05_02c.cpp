#include <gtest/gtest.h>

#include <string>

#include "helpers_sampling_bench.h"

using namespace delta;

namespace {

const char kSeq2[] =
    "sequence seq2; @(posedge fastclk) !clk ##1 clk; endsequence";
const char kDelayedVerdicts[] = "20 fail 40 fail 60 pass 80 fail";

std::string SeqBench(const std::string& items, const std::string& outside = "",
                     const char* clock = "always #10 clk = ~clk;") {
  return outside +
         "module top;\n"
         "  logic clk = 0, fastclk = 1, mycond = 0;\n"
         "  " +
         clock +
         "\n"
         "  always #5 fastclk = ~fastclk;\n"
         "  initial begin #25 mycond = 1; #10 mycond = 0; #20 mycond = 1; "
         "#10 mycond = 0; end\n"
         "  " +
         items +
         "\n"
         "  initial #92 $finish;\n"
         "endmodule\n";
}

std::string Verdict(const std::string& head) {
  return head +
         " $display(\"V%0t pass\", $time); else $display(\"V%0t fail\", "
         "$time);";
}

std::string Covered(const std::string& head) {
  return head + " $display(\"C%0t\", $time);";
}

TEST(SequenceClockedAssertion, AnEdgeAndASequenceEndingThereAgree) {
  const std::string kSeq1 = "sequence seq1; @(posedge clk) 1; endsequence\n  ";
  ExpectLines(SeqBench(Covered("cover property (@(posedge clk) mycond)")), "C",
              "30");
  ExpectLines(SeqBench(kSeq1 + Covered("cover property (@seq1 mycond)")), "C",
              "30");
}

TEST(SequenceClockedAssertion, ASampledSequenceChecksAFastEdgeLater) {
  ExpectLines(SeqBench(std::string(kSeq2) + "\n  " +
                       Covered("cover property (@seq2 mycond)")),
              "C", "60");
}

TEST(SequenceClockedAssertion, ItIsAttemptedOnlyAtTheSequencesEndPoints) {
  ExpectLines(SeqBench(std::string(kSeq2) + "\n  " +
                       Verdict("assert property (@seq2 mycond)")),
              "V", kDelayedVerdicts);
  ExpectLines(SeqBench(std::string(kSeq2) + "\n  " +
                           Verdict("assert property (@seq2 mycond)"),
                       "", ""),
              "V", "");
}

TEST(SequenceClockedAssertion, AnAssumptionChecksAtTheDelayedStep) {
  ExpectLines(SeqBench(std::string(kSeq2) + "\n  " +
                       Verdict("assume property (@seq2 mycond)")),
              "V", kDelayedVerdicts);
}

TEST(SequenceClockedAssertion, AParenthesizedSequenceEventIsTheSame) {
  ExpectLines(SeqBench(std::string(kSeq2) + "\n  " +
                       Covered("cover property (@(seq2) mycond)")),
              "C", "60");
}

TEST(SequenceClockedAssertion, DISABLED_ASequenceInstanceWithActualsClocksIt) {
  ExpectLines(
      SeqBench("sequence s(f, c); @(posedge f) !c ##1 c; endsequence\n  " +
               Verdict("assert property (@(s(fastclk, clk)) mycond)")),
      "V", kDelayedVerdicts);
}

TEST(SequenceClockedAssertion, ANamedPropertyClockedByASequence) {
  ExpectLines(SeqBench(std::string(kSeq2) +
                       "\n  property p; @seq2 mycond; endproperty\n  " +
                       Verdict("assert property (p)")),
              "V", kDelayedVerdicts);
}

TEST(SequenceClockedAssertion, DISABLED_AnImportedSequenceClocksIt) {
  ExpectLines(SeqBench("import pk::*;\n  " +
                           Verdict("assert property (@(sp(fastclk, clk)) "
                                   "mycond)"),
                       "package pk;\n"
                       "  sequence sp(f, c); @(posedge f) !c ##1 c; "
                       "endsequence\n"
                       "endpackage\n"),
              "V", kDelayedVerdicts);
}

TEST(SequenceClockedAssertion,
     DISABLED_AProceduralAssertionWaitsForTheEndPoint) {
  ExpectLines(SeqBench(std::string(kSeq2) + "\n  always @(posedge clk) " +
                       Verdict("assert property (@seq2 mycond)")),
              "V", kDelayedVerdicts);
}

const char kPorts[] = "(input logic clk, fastclk, mycond)";

std::string Unit(const char* kind) {
  return std::string(kind) + " u_unit" + kPorts + ";\n  " + kSeq2 + "\n  " +
         Verdict("assert property (@seq2 mycond)") + "\n  initial #95;\nend" +
         kind + "\n";
}

TEST(SequenceClockedAssertion, AnInterfaceOrProgramsSequenceClocksIt) {
  for (const char* kind : {"interface", "program"}) {
    ExpectLines(SeqBench("u_unit u(clk, fastclk, mycond);", Unit(kind)), "V",
                kDelayedVerdicts);
  }
}

TEST(SequenceClockedAssertion, ACheckersSequenceClocksIt) {
  ExpectLines(SeqBench("ck k(clk, fastclk, mycond);",
                       "checker ck(logic clk, logic fastclk, logic mycond);\n"
                       "  " +
                           std::string(kSeq2) + "\n  " +
                           Verdict("assert property (@seq2 mycond)") +
                           "\nendchecker\n"),
              "V", kDelayedVerdicts);
}

TEST(SequenceClockedAssertion, DISABLED_AGenerateBlocksSequenceClocksIt) {
  ExpectLines(SeqBench("if (1) begin : g " + std::string(kSeq2) + " " +
                       Verdict("assert property (@seq2 mycond)") + " end"),
              "V", kDelayedVerdicts);
}

}  // namespace
