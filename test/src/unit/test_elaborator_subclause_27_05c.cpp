#include <gtest/gtest.h>

#include <cstdint>
#include <set>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kOtherConstruct =
    "has the same name as a generate block in another generate construct in "
    "the same scope";

std::string DeclarationConflict(const std::string& name) {
  std::string message = "generate block '";
  message += name;
  message += "' conflicts with another declaration in the same scope";
  return message;
}

std::string InstantiatedElement(const std::string& element,
                                const std::string& body) {
  std::string src = element;
  src += " e;\n";
  src += body;
  src += "end";
  src += element;
  src += "\nmodule top;\n  e u();\nendmodule\n";
  return src;
}

std::set<std::string> ElaboratedVariableNames(const std::string& src,
                                              ElabFixture& f) {
  auto* design = Elaborate(src, f);
  if (design == nullptr) return {};
  std::set<std::string> names;
  for (const auto& v : design->top_modules[0]->variables) {
    names.insert(std::string(v.name));
  }
  return names;
}

void ExpectErrorAt(const std::string& src, const std::string& message,
                   uint32_t line) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, "27.5"));
}

void ExpectNoError(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConditionalGenerateBlockName, TwoCaseConstructsSharingANameAreReported) {
  const std::string kSrc =
      "module top;\n"
      "  case (1) 1: begin : u int a; end endcase\n"
      "  case (1) 2: begin : u int b; end default: ; endcase\n"
      "endmodule\n";
  ExpectErrorAt(kSrc, kOtherConstruct, 2);
  ExpectErrorAt(kSrc, kOtherConstruct, 3);
}

TEST(ConditionalGenerateBlockName,
     TwoCaseConstructsWithDistinctNamesAreAccepted) {
  ExpectNoError(
      "module top;\n"
      "  case (1) 1: begin : u int a; end endcase\n"
      "  case (1) 2: begin : v int b; end default: begin : v end endcase\n"
      "endmodule\n");
}

TEST(ConditionalGenerateBlockName, ACollisionIsReportedInEachElement) {
  for (const std::string& element : {"interface", "program", "checker"}) {
    for (const std::string& other :
         {"  if (0) begin : u end\n", "  case (1) 1: begin : u end endcase\n",
          "  for (genvar k = 0; k < 1; k++) begin : u end\n"}) {
      if (element == "checker" && other.find("for") != std::string::npos) {
        continue;
      }
      std::string body = "  if (1) begin : u end\n";
      body += other;
      ExpectErrorAt(InstantiatedElement(element, body), kOtherConstruct, 2);
    }
  }
}

TEST(ConditionalGenerateBlockName, DistinctNamesAreAcceptedInEachElement) {
  for (const std::string& element : {"interface", "program", "checker"}) {
    ExpectNoError(InstantiatedElement(element,
                                      "  if (1) begin : u end else begin : u "
                                      "end\n"
                                      "  case (1) 1: begin : v end endcase\n"));
  }
}

TEST(ConditionalGenerateBlockName, AnUnselectedCaseBlockNamedLikeAVariable) {
  ExpectErrorAt(
      "module top #(parameter P = 0) ();\n"
      "  logic dup;\n"
      "  case (P) 1: begin : dup end default: begin end endcase\n"
      "endmodule\n",
      DeclarationConflict("dup"), 3);
}

TEST(ConditionalGenerateBlockName, EachKindOfDeclarationConflicts) {
  const std::string kSrc =
      "module s; endmodule\n"
      "module top #(parameter P = 0) ();\n"
      "  parameter Q = 1;\n"
      "  typedef int T;\n"
      "  s inst();\n"
      "  task tk; endtask\n"
      "  function int fn; return 0; endfunction\n"
      "  if (P) begin : Q end\n"
      "  if (P) begin : T end\n"
      "  if (P) begin : inst end\n"
      "  if (P) begin : tk end\n"
      "  case (P) 1: begin : fn end endcase\n"
      "  if (P) begin : later end\n"
      "  int later;\n"
      "endmodule\n";
  ExpectErrorAt(kSrc, DeclarationConflict("Q"), 8);
  ExpectErrorAt(kSrc, DeclarationConflict("T"), 9);
  ExpectErrorAt(kSrc, DeclarationConflict("inst"), 10);
  ExpectErrorAt(kSrc, DeclarationConflict("tk"), 11);
  ExpectErrorAt(kSrc, DeclarationConflict("fn"), 12);
  ExpectErrorAt(kSrc, DeclarationConflict("later"), 13);
}

TEST(ConditionalGenerateBlockName, ANameNoDeclarationUsesIsAccepted) {
  ExpectNoError(
      "module s; endmodule\n"
      "module top #(parameter P = 0) ();\n"
      "  parameter Q = 1;\n"
      "  typedef int T;\n"
      "  s inst();\n"
      "  if (P) begin : q1 end\n"
      "  case (P) 1: begin : t1 end endcase\n"
      "  int later;\n"
      "endmodule\n");
}

TEST(ConditionalGenerateBlockName,
     ADeclarationConflictIsReportedInEachElement) {
  for (const std::string& element : {"interface", "program", "checker"}) {
    ExpectErrorAt(InstantiatedElement(element,
                                      "  logic d;\n"
                                      "  if (0) begin : d end\n"),
                  DeclarationConflict("d"), 3);
  }
}

TEST(DirectlyNestedConditional, ACaseInsideACaseIsHeldToTheOuterScope) {
  const std::string kSrc =
      "module top;\n"
      "  int u;\n"
      "  case (1) 1: case (1) 1: begin : u end endcase endcase\n"
      "  if (1) begin : k end\n"
      "  case (1) 1: if (1) begin : k end endcase\n"
      "  if (1) case (1) 1: begin : u end endcase\n"
      "endmodule\n";
  ExpectErrorAt(kSrc, DeclarationConflict("u"), 3);
  ExpectErrorAt(kSrc, kOtherConstruct, 5);
  ExpectErrorAt(kSrc, DeclarationConflict("u"), 6);
}

TEST(DirectlyNestedConditional, ItsBlocksMayShareTheOuterConstructsName) {
  ExpectNoError(
      "module top #(parameter P = 1, Q = 1) ();\n"
      "  case (P)\n"
      "    1: if (Q) begin : s end else begin : s end\n"
      "    2: case (Q) 1: begin : s end endcase\n"
      "    default: begin : s end\n"
      "  endcase\n"
      "  if (P) case (Q) 1: begin : v end default: begin : v end endcase\n"
      "  else begin : v end\n"
      "endmodule\n");
}

TEST(DirectNestingAndLoops, AConditionalHoldingABareLoopIsItsOwnScope) {
  ExpectNoError(
      "module top;\n"
      "  int b = 5;\n"
      "  if (1) for (genvar i = 0; i < 1; i++) begin : b int x = 7; end\n"
      "  if (1) for (genvar i = 0; i < 1; i++) begin : b int x = 8; end\n"
      "endmodule\n");
}

TEST(DirectNestingAndLoops, ABareConditionalInAConditionalIsNotItsOwnScope) {
  const std::string kSrc =
      "module top;\n"
      "  if (1) if (1) begin : b end\n"
      "  if (1) if (1) begin : b end\n"
      "endmodule\n";
  ExpectErrorAt(kSrc, kOtherConstruct, 2);
  ExpectErrorAt(kSrc, kOtherConstruct, 3);
}

TEST(DirectNestingAndLoops, ALoopHoldingABareConditionalIsAScopePerIteration) {
  ExpectNoError(
      "module top;\n"
      "  int x = 5;\n"
      "  for (genvar i = 0; i < 2; i++) if (1) begin : x int y = i; end\n"
      "  for (genvar j = 0; j < 2; j++) if (1) begin : x int y = j; end\n"
      "endmodule\n");
}

TEST(ConditionalGenerateScope, ABareElseItemIsItsOwnScope) {
  ExpectNoError(
      "module top;\n"
      "  int b = 5;\n"
      "  if (0) int a; else int b = 9;\n"
      "  if (0) int a; else int b = 8;\n"
      "  case (1) 1: int b = 7; endcase\n"
      "endmodule\n");
}

TEST(ConditionalGenerateScheme, ARealVariableInAConditionIsReported) {
  const std::string kSrc =
      "module top;\n"
      "  real r;\n"
      "  if (r > 1.0) begin : a end\n"
      "  case (r < 1.0) 1'b1: begin : b end endcase\n"
      "endmodule\n";
  ExpectErrorAt(kSrc, "generate-if condition is not constant", 3);
  ExpectErrorAt(kSrc, "generate-case selector is not constant", 4);
}

TEST(DirectNestingAndLoops, TheBareLoopsBlocksSitUnderTheConditionalsBlock) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames(
                "module top;\n"
                "  int b;\n"
                "  if (1) for (genvar i = 0; i < 2; i++) begin : b int x; end\n"
                "endmodule\n",
                f),
            (std::set<std::string>{"b", "genblk1_b_0_x", "genblk1_b_1_x"}));
  EXPECT_FALSE(f.has_errors);
}

TEST(DirectNestingAndLoops, TheBareConditionalsBlockSitsUnderEachIteration) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames(
                "module top;\n"
                "  int x;\n"
                "  for (genvar i = 0; i < 2; i++) if (1) begin : x int y; end\n"
                "endmodule\n",
                f),
            (std::set<std::string>{"x", "genblk1_0_x_y", "genblk1_1_x_y"}));
  EXPECT_FALSE(f.has_errors);
}

TEST(ConditionalGenerateScope, ABareElseItemIsNamedUnderItsBlock) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames("module top;\n"
                                    "  int b;\n"
                                    "  if (0) int a; else int b;\n"
                                    "endmodule\n",
                                    f),
            (std::set<std::string>{"b", "genblk1_b"}));
  EXPECT_FALSE(f.has_errors);
}

TEST(DirectlyNestedConditional, AnUnnamedInnerBlockTakesTheOuterNumber) {
  ElabFixture f;
  EXPECT_EQ(ElaboratedVariableNames(
                "module top;\n"
                "  case (1) 1: if (1) begin int v; end endcase\n"
                "  if (1) case (1) 1: begin int w; end endcase\n"
                "  case (1) 1: case (1) 1: begin int z; end endcase endcase\n"
                "  if (0) begin int n; end\n"
                "  if (1) begin int k; end\n"
                "endmodule\n",
                f),
            (std::set<std::string>{"genblk1_v", "genblk2_w", "genblk3_z",
                                   "genblk5_k"}));
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
