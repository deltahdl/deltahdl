#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kNoLvalue =
    "the output actual of the formal 'failure' of checker 'c' is neither a "
    "variable nor a net lvalue";

const char* const kOutputCheckers =
    "checker c(logic clk, output bit failure);\n"
    "  a1: assert property (@(posedge clk) 1) failure = 1'b0;\n"
    "    else failure = 1'b1;\n"
    "endchecker\n"
    "checker c2(logic clk, output bit [1:0] failure);\n"
    "  a1: assert property (@(posedge clk) 1) failure = 2'b00;\n"
    "    else failure = 2'b11;\n"
    "endchecker\n";

const char* const kOutputPackage =
    "package pk;\n"
    "  typedef enum bit {E0, E1} pe_t;\n"
    "  parameter bit PP = 0;\n"
    "  bit v;\n"
    "endpackage\n";

void ExpectOutputs(const std::string& src,
                   const std::vector<std::string>& reported,
                   const std::vector<std::string>& accepted) {
  ElabFixture f;
  ElaborateSrc(src, f, "m");
  for (const auto& marker : reported) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoLvalue,
                              LineHolding(src, marker), "17.3"))
        << marker << "\n"
        << src;
  }
  for (const auto& marker : accepted) {
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), LineHolding(src, marker)))
        << marker << "\n"
        << src;
  }
}

std::string OutputModule(const std::string& items) {
  return std::string(kOutputCheckers) + kOutputPackage +
         "module sub;\n  bit x;\nendmodule\n"
         "module m;\n"
         "  logic clk;\n"
         "  bit v, a, b;\n"
         "  bit [3:0] vec;\n"
         "  int i;\n"
         "  wire w;\n"
         "  wire [3:0] wv;\n"
         "  typedef bit [1:0] pair_t;\n" +
         items + "endmodule\n";
}

TEST(CheckerOutputActual, ANetAndItsConstantSelectsAreAccepted) {
  ExpectOutputs(OutputModule("  c u1(clk, w);\n"
                             "  c u2(clk, wv[1]);\n"
                             "  c2 u3(clk, wv[1:0]);\n"
                             "  c2 u4(clk, {wv[2], wv[3]});\n"
                             "  c2 u5(clk, {w, v});\n"),
                {}, {"c u1(", "c u2(", "c2 u3(", "c2 u4(", "c2 u5("});
}

TEST(CheckerOutputActual, VariableSelectsAreAccepted) {
  ExpectOutputs(OutputModule("  c u1(clk, vec[i]);\n"
                             "  c2 u2(clk, vec[3:2]);\n"
                             "  c2 u3(clk, vec[0+:2]);\n"),
                {}, {"c u1(", "c2 u2(", "c2 u3("});
}

TEST(CheckerOutputActual, AHierarchicalOrPackageVariableIsAccepted) {
  ExpectOutputs(OutputModule("  sub s();\n"
                             "  c u1(clk, s.x);\n"
                             "  c u2(clk, pk::v);\n"),
                {}, {"c u1(", "c u2("});
}

TEST(CheckerOutputActual, DISABLED_AStreamOrAnAssignmentPatternIsAccepted) {
  ExpectOutputs(OutputModule("  c2 u1(clk, {>>{a, b}});\n"
                             "  c2 u2(clk, '{a, b});\n"
                             "  c2 u3(clk, pair_t'{a, b});\n"),
                {}, {"c2 u1(", "c2 u2(", "c2 u3("});
}

TEST(CheckerOutputActual, AnImplicitConnectionToAVariableIsAccepted) {
  for (const char* instance : {"  c u(.clk, .failure);\n", "  c u(.*);\n"}) {
    SCOPED_TRACE(instance);
    ExpectOutputs(std::string(kOutputCheckers) +
                      "module m;\n"
                      "  logic clk;\n"
                      "  bit failure;\n" +
                      instance + "endmodule\n",
                  {}, {"c u("});
  }
}

const char* const kModuleForbidden[] = {
    "1'b0", "f()", "P", "LP", "A", "pk::E1", "pk::PP", "SP", "wv[i]",
};

std::string ForbiddenInstances(const char* const* forms, size_t count,
                               std::vector<std::string>& reported,
                               const std::string& indent) {
  std::string items;
  for (size_t n = 0; n < count; ++n) {
    std::string marker = "c u" + std::to_string(n) + "(";
    items += indent + marker + "clk, " + forms[n] + ");\n";
    reported.push_back(marker);
  }
  return items;
}

const char* const kModuleDeclarations =
    "  parameter bit P = 0;\n"
    "  localparam bit LP = 0;\n"
    "  typedef enum bit {A, B} e_t;\n"
    "  specparam SP = 1;\n"
    "  function bit f();\n"
    "    return 0;\n"
    "  endfunction\n";

TEST(CheckerOutputActual,
     DISABLED_ANamedConstantOrAVariableIndexedNetIsReported) {
  std::vector<std::string> reported;
  std::string items =
      kModuleDeclarations +
      ForbiddenInstances(kModuleForbidden, std::size(kModuleForbidden),
                         reported, "  ") +
      "  c uok(clk, v);\n";
  ExpectOutputs(OutputModule(items), reported, {"c uok("});
}

TEST(CheckerOutputActual, DISABLED_AConcatenationHoldingAConstantIsReported) {
  std::string src = OutputModule(std::string(kModuleDeclarations) +
                                 "  bit v1, v2, v3;\n  c2 u1(clk, {v1, P});\n"
                                 "  c2 u2(clk, {v2, 1'b0});\n"
                                 "  c2 uok(clk, {v3, a});\n");
  ElabFixture f;
  ElaborateSrc(src, f, "m");
  for (const char* marker : {"c2 u1(", "c2 u2("}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "the output actual of the formal 'failure' of "
                              "checker 'c2' is neither a variable nor a net "
                              "lvalue",
                              LineHolding(src, marker), "17.3"))
        << marker;
  }
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), LineHolding(src, "c2 uok(")));
}

TEST(CheckerOutputActual, DISABLED_AGenvarIsReported) {
  ExpectOutputs(OutputModule("  for (genvar gi = 0; gi < 1; gi++) begin : lg\n"
                             "    c ug(clk, gi);\n"
                             "  end\n"),
                {"c ug("}, {});
}

TEST(CheckerOutputActual, DISABLED_AParameterConnectedByNameIsReported) {
  ExpectOutputs(OutputModule(std::string(kModuleDeclarations) +
                             "  c u1(.clk(clk), .failure(P));\n"
                             "  c uok(.clk(clk), .failure(v));\n"),
                {"c u1("}, {"c uok("});
}

TEST(CheckerOutputActual, DISABLED_AnImplicitConnectionToAParameterIsReported) {
  ExpectOutputs(std::string(kOutputCheckers) +
                    "module m;\n"
                    "  logic clk;\n"
                    "  parameter bit failure = 0;\n"
                    "  c u1(.clk, .failure);\n"
                    "  c u2(.*);\n"
                    "endmodule\n",
                {"c u1(", "c u2("}, {});
}

const char* const kScopeForbidden[] = {"1'b0", "f()", "P", "A", "pk::E1"};

const char* const kScopeDeclarations =
    "  parameter bit P = 0;\n"
    "  typedef enum bit {A, B} e_t;\n"
    "  function bit f();\n"
    "    return 0;\n"
    "  endfunction\n"
    "  bit v;\n";

TEST(CheckerOutputActual,
     DISABLED_EachConstantIsReportedInAnInterfaceOrProgram) {
  for (const char* keyword : {"interface", "program"}) {
    SCOPED_TRACE(keyword);
    std::vector<std::string> reported;
    std::string body = ForbiddenInstances(
        kScopeForbidden, std::size(kScopeForbidden), reported, "  ");
    ExpectOutputs(std::string(kOutputCheckers) + kOutputPackage + keyword +
                      " box(input logic clk);\n" + kScopeDeclarations + body +
                      "  c uok(clk, v);\nend" + keyword +
                      "\nmodule m;\n  logic clk;\n  box b(clk);\nendmodule\n",
                  reported, {"c uok("});
  }
}

TEST(CheckerOutputActual, DISABLED_EachConstantIsReportedInAChecker) {
  const char* const kCheckerForbidden[] = {"1'b0", "f()", "A", "pk::E1",
                                           "pk::PP"};
  std::vector<std::string> reported;
  std::string body = ForbiddenInstances(
      kCheckerForbidden, std::size(kCheckerForbidden), reported, "  ");
  ExpectOutputs(std::string(kOutputCheckers) + kOutputPackage +
                    "checker box(logic clk);\n"
                    "  typedef enum bit {A, B} e_t;\n"
                    "  function bit f();\n"
                    "    return 0;\n"
                    "  endfunction\n"
                    "  bit v;\n" +
                    body +
                    "  c uok(clk, v);\n"
                    "endchecker\n"
                    "module m;\n  logic clk;\n  box b(clk);\nendmodule\n",
                reported, {"c uok("});
}

TEST(CheckerOutputActual, DISABLED_EachConstantIsReportedInAGenerateBlock) {
  const char* const kOpens[] = {
      "  if (1) begin : g\n", "  case (1)\n  1: begin : g\n",
      "  for (genvar gi = 0; gi < 1; gi++) begin : g\n"};
  const char* const kCloses[] = {"  end\n", "  end\n  endcase\n", "  end\n"};
  for (size_t n = 0; n < 3; ++n) {
    SCOPED_TRACE(kOpens[n]);
    std::vector<std::string> reported;
    std::string body = ForbiddenInstances(
        kScopeForbidden, std::size(kScopeForbidden), reported, "    ");
    reported.push_back("c uop(");
    ExpectOutputs(OutputModule(std::string(kModuleDeclarations) + kOpens[n] +
                               body + "    c uok(clk, v);\n" +
                               "    c uop(clk, a & b);\n" + kCloses[n]),
                  reported, {"c uok("});
  }
}

TEST(CheckerOutputActual,
     DISABLED_EachConstantIsReportedFromAProceduralInstance) {
  for (const char* procedure : {"always @(posedge clk)", "initial"}) {
    SCOPED_TRACE(procedure);
    std::vector<std::string> reported;
    std::string body = ForbiddenInstances(
        kScopeForbidden, std::size(kScopeForbidden), reported, "    ");
    ExpectOutputs(
        OutputModule(std::string(kModuleDeclarations) + "  " + procedure +
                     " begin\n" + body + "    c uok(clk, v);\n  end\n"),
        reported, {"c uok("});
  }
}

const char* const kPortChecker =
    "checker pc(logic clk, logic a, k = 1'b1);\n"
    "  a1: assert property (@(posedge clk) a && k);\n"
    "endchecker\n";

TEST(CheckerImplicitConnection, ANameWithNoDeclarationIsReported) {
  std::string src = std::string(kPortChecker) +
                    "module m;\n"
                    "  logic clk, a;\n"
                    "  pc u1(.clk, .a, .k);\n"
                    "  pc u2(.clk, .a, .k());\n"
                    "endmodule\n";
  ElabFixture f;
  ElaborateSrc(src, f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "implicit named port connection '.k' requires "
                            "signal 'k' to be declared in the instantiating "
                            "scope",
                            LineHolding(src, "pc u1("), "23.3.2.3"));
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), LineHolding(src, "pc u2(")));
}

TEST(CheckerImplicitConnection,
     DISABLED_AWildcardFindingNothingForAFormalWithNoDefault) {
  std::string src =
      "checker nd(logic clk, logic a, logic k);\n"
      "  a1: assert property (@(posedge clk) a && k);\n"
      "endchecker\n" +
      std::string(kPortChecker) +
      "module m;\n"
      "  logic clk, a;\n"
      "  nd u1(.*);\n"
      "  pc u2(.*);\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(src, f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "finds no declaration of 'k'",
                            LineHolding(src, "nd u1("), "23.3.2.4"));
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), LineHolding(src, "pc u2(")));
}

}  // namespace
