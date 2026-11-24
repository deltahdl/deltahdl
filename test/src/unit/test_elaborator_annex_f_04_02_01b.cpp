#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string Checker(const std::string& header, const std::string& item) {
  return "checker chk(" + header + "\n  " + item +
         "\nendchecker\n"
         "checker whole(input logic clk, output logic [3:0] k);\n"
         "  always_ff @(posedge clk) k <= 1;\nendchecker\n"
         "checker one(input logic clk, output logic o);\n"
         "  always_ff @(posedge clk) o <= 1;\nendchecker\n";
}

std::vector<std::string> InputHeaders() {
  return {"input logic clk, input logic [3:0] k, input logic d);",
          "input logic clk, logic [3:0] k, logic d);",
          "logic [3:0] k, logic clk, logic d);"};
}

std::vector<std::string> WritableHeaders() {
  return {"input logic clk, input logic d, output logic [3:0] k);",
          "input logic clk, input logic d); logic [3:0] k;"};
}

void ExpectReported(const std::string& item) {
  for (const std::string& header : InputHeaders()) {
    ElabFixture f;
    ElaborateSrc(Checker(header, item), f, "chk");
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "input formal argument 'k' cannot be modified "
                              "inside checker 'chk'",
                              2, "17.2"))
        << header << item;
  }
}

void ExpectAccepted(const std::string& item) {
  for (const std::string& header : WritableHeaders()) {
    ElabFixture f;
    ElaborateSrc(Checker(header, item), f, "chk");
    EXPECT_FALSE(f.has_errors) << header << item;
  }
}

std::vector<std::string> ContinuousWrites() { return {"assign k = d;"}; }

std::vector<std::string> NonblockingWrites() {
  return {"always_ff @(posedge clk) k <= 1;"};
}

std::vector<std::string> BlockingWrites() {
  return {"always_comb k = d;", "always_latch if (d) k = 1;"};
}

std::vector<std::string> CombinationalSteps() {
  return {"always_comb k++;", "always_comb k--;", "always_comb ++k;",
          "always_comb --k;"};
}

std::vector<std::string> ClockedSteps() {
  return {"always_ff @(posedge clk) k++;", "always_ff @(posedge clk) k--;",
          "always_ff @(posedge clk) ++k;", "always_ff @(posedge clk) --k;"};
}

std::vector<std::string> CompoundWrites() {
  return {"always_comb k += 1;", "always_comb k <<= 1;"};
}

std::vector<std::string> SelectWrites() {
  return {"always_ff @(posedge clk) k[0] <= 1;",
          "always_ff @(posedge clk) k[2:1] <= 1;",
          "always_ff @(posedge clk) k[0+:2] <= 1;"};
}

std::vector<std::string> ConcatenationWrites() {
  return {"logic w; always_ff @(posedge clk) {w, k} <= 5;"};
}

std::vector<std::string> ItemActionWrites() {
  return {"assert property (@(posedge clk) d) else k = 1;",
          "assert property (@(posedge clk) d) k = 1;",
          "assume property (@(posedge clk) d) else k = 1;",
          "assume property (@(posedge clk) d) k = 1;",
          "cover property (@(posedge clk) d) k = 1;"};
}

std::vector<std::string> ProcedureActionWrites() {
  return {"always_ff @(posedge clk) assert property (d) else k = 1;",
          "always_ff @(posedge clk) assert property (d) k = 1;"};
}

std::vector<std::string> DeferredActionWrites() {
  return {"always_comb assert #0 (d) else k = 1;",
          "always_comb assert final (d) else k = 1;"};
}

std::vector<std::string> OutputConnections() {
  return {"whole i(clk, k);",   "whole i(.clk(clk), .k(k));",
          "whole i(.clk, .k);", "whole i(.*);",
          "one i(clk, k[0]);",  "one i(.clk(clk), .o(k[0]));"};
}

void ExpectEachReported(const std::vector<std::string>& writes) {
  for (const std::string& write : writes) ExpectReported(write);
}

void ExpectEachAccepted(const std::vector<std::string>& writes) {
  for (const std::string& write : writes) ExpectAccepted(write);
}

TEST(TypedInputWrite, AContinuousAssignmentIsReported) {
  ExpectEachReported(ContinuousWrites());
}

TEST(TypedInputWrite, ANonblockingAssignmentIsReported) {
  ExpectEachReported(NonblockingWrites());
}

TEST(TypedInputWrite, ABlockingAssignmentIsReported) {
  ExpectEachReported(BlockingWrites());
}

TEST(TypedInputWrite, AnInitialAssignmentIsReported) {
  ExpectReported("initial k = 1;");
}

TEST(TypedInputWrite, DISABLED_ACombinationalStepIsReported) {
  ExpectEachReported(CombinationalSteps());
}

TEST(TypedInputWrite, DISABLED_AClockedStepIsReported) {
  ExpectEachReported(ClockedSteps());
}

TEST(TypedInputWrite, ACompoundAssignmentIsReported) {
  ExpectEachReported(CompoundWrites());
}

TEST(TypedInputWrite, AnAssignmentToASelectIsReported) {
  ExpectEachReported(SelectWrites());
}

TEST(TypedInputWrite, AnAssignmentToAConcatenationIsReported) {
  ExpectEachReported(ConcatenationWrites());
}

TEST(TypedInputWrite, DISABLED_AConcurrentActionInTheBodyIsReported) {
  ExpectEachReported(ItemActionWrites());
}

TEST(TypedInputWrite, AConcurrentActionInAProcedureIsReported) {
  ExpectEachReported(ProcedureActionWrites());
}

TEST(TypedInputWrite, ADeferredActionIsReported) {
  ExpectEachReported(DeferredActionWrites());
}

TEST(TypedInputWrite, DISABLED_ANestedCheckersOutputConnectionIsReported) {
  ExpectEachReported(OutputConnections());
}

TEST(WritableTargetWrite, AssignmentsAreAccepted) {
  ExpectEachAccepted(ContinuousWrites());
  ExpectEachAccepted(NonblockingWrites());
  ExpectEachAccepted(BlockingWrites());
  ExpectEachAccepted(CompoundWrites());
  ExpectEachAccepted(SelectWrites());
  ExpectEachAccepted(ConcatenationWrites());
}

TEST(WritableTargetWrite, CombinationalStepsAreAccepted) {
  ExpectEachAccepted(CombinationalSteps());
}

TEST(WritableTargetWrite, ConcurrentActionsAreAccepted) {
  ExpectEachAccepted(ItemActionWrites());
}

TEST(WritableTargetWrite, ANestedCheckersOutputConnectionIsAccepted) {
  ExpectEachAccepted(OutputConnections());
}

std::vector<std::string> GenerateItems() {
  std::vector<std::string> items;
  for (const std::vector<std::string>& writes :
       {ContinuousWrites(), NonblockingWrites(), BlockingWrites(),
        CombinationalSteps(), CompoundWrites(), SelectWrites(),
        ConcatenationWrites(), ItemActionWrites(), OutputConnections()}) {
    items.insert(items.end(), writes.begin(), writes.end());
  }
  return items;
}

std::vector<std::string> ReportedGenerateItems() {
  std::vector<std::string> items = GenerateItems();
  for (const std::vector<std::string>& writes :
       {ClockedSteps(), ProcedureActionWrites(), DeferredActionWrites()}) {
    items.insert(items.end(), writes.begin(), writes.end());
  }
  return items;
}

std::string Conditional(const std::string& item) {
  return "if (1) begin : g " + item + " end";
}

std::string Case(const std::string& item) {
  return "case (1) 1: begin : g " + item + " end endcase";
}

std::string Loop(const std::string& item) {
  return "for (genvar i = 0; i < 1; i++) begin : g " + item + " end";
}

TEST(TypedInputWrite, DISABLED_EachWriteInAConditionalGenerateIsReported) {
  for (const std::string& item : ReportedGenerateItems()) {
    ExpectReported(Conditional(item));
  }
}

TEST(TypedInputWrite, DISABLED_EachWriteInACaseGenerateIsReported) {
  for (const std::string& item : ReportedGenerateItems()) {
    ExpectReported(Case(item));
  }
}

TEST(TypedInputWrite, DISABLED_EachWriteInALoopGenerateIsReported) {
  for (const std::string& item : ReportedGenerateItems()) {
    ExpectReported(Loop(item));
  }
}

TEST(WritableTargetWrite, EachWriteInAGenerateBlockIsAccepted) {
  for (const std::string& item : GenerateItems()) {
    ExpectAccepted(Conditional(item));
    ExpectAccepted(Case(item));
    ExpectAccepted(Loop(item));
  }
}

}  // namespace
