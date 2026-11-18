#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kArrayConflict =
    "generate block array 'a' conflicts with an existing declaration in the "
    "same scope";
constexpr const char* kReusedGenvar =
    "genvar 'i' is already in use by an enclosing loop generate construct";
constexpr const char* kDifferentGenvars =
    "generate-for init and step assign different genvars";
constexpr const char* kOutsideScheme =
    "is referenced outside a loop generate scheme";
constexpr const char* kUnnamedReachIn =
    "hierarchical name reaches into unnamed generate block 'genblk1'";

void ExpectErrorAt(const std::string& src, const std::string& message,
                   uint32_t line, const std::string& subclause) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, subclause));
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

void ExpectNoError(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(LoopGenerateArrayName, ANetOfTheSameNameIsReported) {
  ExpectErrorAt(
      "module top;\n"
      "  wire a;\n"
      "  for (genvar i = 0; i < 2; i++) begin : a end\n"
      "endmodule\n",
      kArrayConflict, 3, "27.4");
}

TEST(LoopGenerateArrayName, AParameterOfTheSameNameIsReported) {
  ExpectErrorAt(
      "module top;\n"
      "  parameter int a = 1;\n"
      "  for (genvar i = 0; i < 2; i++) begin : a end\n"
      "endmodule\n",
      kArrayConflict, 3, "27.4");
}

TEST(LoopGenerateArrayName, ALaterDeclarationOfTheSameNameIsReported) {
  ExpectErrorAt(
      "module top;\n"
      "  for (genvar i = 0; i < 2; i++) begin : a end\n"
      "  logic a;\n"
      "endmodule\n",
      kArrayConflict, 2, "27.4");
}

TEST(LoopGenerateArrayName, ANamedConditionalBlockOfTheSameNameIsReported) {
  ExpectErrorAt(
      "module top;\n"
      "  if (1) begin : a end\n"
      "  for (genvar i = 0; i < 2; i++) begin : a end\n"
      "endmodule\n",
      "generate block 'a' has the same name as a generate block in another "
      "generate construct in the same scope",
      2, "27.5");
}

TEST(LoopGenerateArrayName, DistinctNamesBesideTheArrayAreAccepted) {
  ExpectNoError(
      "module top;\n"
      "  wire n;\n"
      "  parameter int p = 1;\n"
      "  if (1) begin : c end\n"
      "  for (genvar i = 0; i < 2; i++) begin : a end\n"
      "  logic v;\n"
      "endmodule\n");
}

TEST(LoopGenerateGenvarValues, AValueTakenAgainAfterOthersIsReported) {
  ExpectErrorAt(
      "module top;\n"
      "  for (genvar i = 0; i < 2; i = (i + 1) % 2) begin : a end\n"
      "endmodule\n",
      "generate-for genvar value is repeated during evaluation", 2, "27.4");
}

TEST(LoopGenerateGenvarValues, AWrappingStepThatExitsFirstIsAccepted) {
  ExpectNoError(
      "module top;\n"
      "  for (genvar i = 0; i < 2; i = (i + 1) % 5) begin : a end\n"
      "endmodule\n");
}

TEST(LoopGenerateNesting, ReuseThroughAConditionalConstructIsReported) {
  ExpectErrorAt(
      "module top;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin : a\n"
      "    if (1) begin : b\n"
      "      for (i = 0; i < 2; i = i + 1) begin : c end\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      kReusedGenvar, 5, "27.4");
}

TEST(LoopGenerateNesting, AnInlineGenvarOfTheOuterIndexNameIsReported) {
  for (const std::string& outer : {"i = 0", "genvar i = 0"}) {
    std::string declared = outer == "i = 0" ? "  genvar i;\n" : "";
    std::string src = "module top;\n";
    src += declared;
    src += "  for (";
    src += outer;
    src +=
        "; i < 2; i = i + 1) begin : a\n"
        "    for (genvar i = 0; i < 2; i = i + 1) begin : c end\n"
        "  end\n"
        "endmodule\n";
    ExpectErrorAt(src, kReusedGenvar, declared.empty() ? 3 : 4, "27.4");
  }
}

TEST(LoopGenerateNesting, DISABLED_AReusedGenvarIsReportedOnce) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 3; i = i + 1) begin : a\n"
      "    for (i = 0; i < 2; i = i + 1) begin : b end\n"
      "  end\n"
      "endmodule\n",
      f);
  size_t count = 0;
  for (const auto& diag : f.diag.Diagnostics()) {
    if (diag.message.find(kReusedGenvar) != std::string::npos) ++count;
  }
  EXPECT_EQ(count, 1u);
}

TEST(LoopGenerateHeader, AnIterationOnAnotherGenvarIsReportedInEveryForm) {
  for (const std::string& step : {"j += 1", "j--", "++j", "--j", "j -= 1"}) {
    ExpectErrorAt("module top;\n  genvar i, j;\n  for (i = 0; i < 3; " + step +
                      ") begin : a end\nendmodule\n",
                  kDifferentGenvars, 3, "27.4");
  }
}

TEST(LoopGenerateHeader, AnInlineGenvarStepOnAnotherGenvarIsReported) {
  ExpectErrorAt(
      "module top;\n"
      "  genvar j;\n"
      "  for (genvar i = 0; i < 3; j++) begin : a end\n"
      "endmodule\n",
      kDifferentGenvars, 3, "27.4");
}

TEST(LoopGenerateHeader, AnIterationOnTheSameGenvarIsAcceptedInEveryForm) {
  for (const std::string& step : {"i += 1", "i++", "++i", "i = i + 1"}) {
    ExpectNoError("module top;\n  genvar i;\n  for (i = 0; i < 3; " + step +
                  ") begin : a end\n  for (genvar k = 3; k > 0; k--) begin : "
                  "b end\nendmodule\n");
  }
}

TEST(LoopGenerateHeader, ADeclaredGenvarsInitReadingItselfIsReported) {
  ExpectErrorAt(
      "module top;\n"
      "  genvar i;\n"
      "  for (i = i + 1; i < 3; i = i + 1) begin : a end\n"
      "endmodule\n",
      "generate-for init reads the loop's own genvar on its right-hand side", 3,
      "27.4");
}

TEST(LoopGenerateHeader, ADeclaredGenvarsInitReadingAParameterIsAccepted) {
  ExpectNoError(
      "module top;\n"
      "  localparam int P = 1;\n"
      "  genvar i;\n"
      "  for (i = P + 1; i < 3; i = i + 1) begin : a end\n"
      "endmodule\n");
}

TEST(LoopGenerateIndexDeclaration, AnUndeclaredIndexIsReportedInEachElement) {
  for (const std::string& element : {"interface", "program", "checker"}) {
    ExpectErrorAt(
        InstantiatedElement(element,
                            "  for (k = 0; k < 2; k = k + 1) begin : a end\n"),
        "loop generate index 'k' is declared by no genvar "
        "declaration",
        2, "27.4");
  }
}

TEST(LoopGenerateIndexDeclaration, ADeclaredIndexIsAcceptedInEachElement) {
  for (const std::string& element : {"interface", "program", "checker"}) {
    ExpectNoError(InstantiatedElement(
        element,
        "  genvar p;\n"
        "  for (p = 0; p < 2; p++) begin : b end\n"
        "  for (genvar m = 0; m < 2; m++) begin : c end\n"));
  }
}

TEST(GenvarReference, AReadInASubroutineIsReported) {
  const std::string kSrc =
      "module top;\n"
      "  genvar i;\n"
      "  function int f();\n"
      "    return i;\n"
      "  endfunction\n"
      "  task t();\n"
      "    $display(i);\n"
      "  endtask\n"
      "endmodule\n";
  ExpectErrorAt(kSrc, std::string("genvar 'i' ") + kOutsideScheme, 4, "27.4");
  ExpectErrorAt(kSrc, std::string("genvar 'i' ") + kOutsideScheme, 7, "27.4");
}

TEST(GenvarReference, DISABLED_AHierarchicalReadIsReported) {
  ExpectErrorAt(
      "module sub;\n"
      "  genvar i;\n"
      "endmodule\n"
      "module top;\n"
      "  sub u();\n"
      "  int k;\n"
      "  initial k = u.i;\n"
      "endmodule\n",
      kOutsideScheme, 7, "27.4");
}

TEST(GenvarReference, DISABLED_AnotherGenvarReadInALoopBlockIsReported) {
  const std::string kSrc =
      "module top;\n"
      "  genvar i, j;\n"
      "  int k;\n"
      "  for (i = 0; i < 2; i = i + 1) begin : g\n"
      "    localparam int L = j;\n"
      "    initial k = j;\n"
      "  end\n"
      "endmodule\n";
  ExpectErrorAt(kSrc, std::string("genvar 'j' ") + kOutsideScheme, 5, "27.4");
  ExpectErrorAt(kSrc, std::string("genvar 'j' ") + kOutsideScheme, 6, "27.4");
}

TEST(GenvarReference, AReadInAnInterfaceOrProgramIsReported) {
  for (const std::string& element : {"interface", "program"}) {
    ExpectErrorAt(InstantiatedElement(element,
                                      "  genvar i;\n"
                                      "  int k;\n"
                                      "  initial k = i;\n"),
                  std::string("genvar 'i' ") + kOutsideScheme, 4, "27.4");
  }
}

TEST(GenvarReference, AReadInItsLoopInAnInterfaceOrProgramIsAccepted) {
  for (const std::string& element : {"interface", "program"}) {
    ExpectNoError(InstantiatedElement(element,
                                      "  genvar i;\n"
                                      "  int k;\n"
                                      "  for (i = 0; i < 2; i++) begin : g\n"
                                      "    initial k = i;\n"
                                      "  end\n"));
  }
}

TEST(LoopIndexLocalparam, AnAssignmentToItIsReported) {
  ExpectErrorAt(
      "module top;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    initial i = 5;\n"
      "  end\n"
      "endmodule\n",
      "assignment to constant 'i'", 3, "6.20");
}

TEST(LoopIndexLocalparam, DISABLED_ADefparamOfItIsReported) {
  ExpectErrorAt(
      "module top;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "  end\n"
      "  defparam g[0].i = 7;\n"
      "endmodule\n",
      "defparam cannot override a local parameter", 4, "23.10.1");
}

TEST(UnnamedGenerateBlockReach, AModuleRootedPathIntoALoopBlockIsReported) {
  ExpectErrorAt(
      "module t;\n"
      "  for (genvar i = 0; i < 2; i++) begin\n"
      "    int b = 1;\n"
      "  end\n"
      "  int r;\n"
      "  initial r = t.genblk1[0].b;\n"
      "endmodule\n",
      kUnnamedReachIn, 6, "27.6");
}

TEST(UnnamedGenerateBlockReach, DISABLED_APathThroughANamedBlockIsReported) {
  for (const std::string& decl : {"", "    int genblk1;\n"}) {
    ExpectErrorAt("module t;\n  for (genvar i = 0; i < 2; i++) begin : g\n" +
                      decl +
                      "    if (1) begin\n"
                      "      int a = 1;\n"
                      "    end\n"
                      "  end\n"
                      "  int r;\n"
                      "  initial r = g[0].genblk1.a;\n"
                      "endmodule\n",
                  kUnnamedReachIn, decl.empty() ? 8 : 9, "27.6");
  }
}

TEST(UnnamedGenerateBlockReach, AReachInIsReportedInEachElement) {
  for (const std::string& element : {"interface", "program", "checker"}) {
    std::string read = element == "checker" ? "  always_comb r = genblk1.a;\n"
                                            : "  initial r = genblk1.a;\n";
    std::string body =
        "  if (1) begin\n"
        "    int a = 1;\n"
        "  end\n"
        "  int r;\n";
    body += read;
    ExpectErrorAt(InstantiatedElement(element, body), kUnnamedReachIn, 6,
                  "27.6");
  }
}

TEST(UnnamedGenerateBlockReach, DISABLED_AReachInFromAnInitializerIsReported) {
  for (const std::string& element : {"module", "checker"}) {
    ExpectErrorAt(InstantiatedElement(element,
                                      "  if (1) begin\n"
                                      "    int a = 1;\n"
                                      "  end\n"
                                      "  int r = genblk1.a;\n"),
                  kUnnamedReachIn, 5, "27.6");
  }
}

}  // namespace
