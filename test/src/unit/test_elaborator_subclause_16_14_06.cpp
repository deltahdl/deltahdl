#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kNoClockReport =
    "no clock is inferred for the procedural concurrent assertion";

TEST(ProceduralClockInference, NoEdgeAndAReferencedSignalInferNoClock) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clock, input logic reset, input logic d1);\n"
      "  logic q;\n"
      "  int cnt;\n"
      "  property r3;\n"
      "    q != d1;\n"
      "  endproperty\n"
      "  always_ff @(clock iff reset == 0 or posedge reset) begin\n"
      "    cnt <= reset ? 0 : cnt + 1;\n"
      "    q <= d1;\n"
      "    r3_p: assert property (r3);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNoClockReport, 10, "16.14.6"));
}

TEST(ProceduralClockInference, ADelayAndASecondEventControlInferNoClock) {
  ElabFixture f;
  Elaborate(
      "module m(input logic mclk, input logic d1);\n"
      "  logic q, q1;\n"
      "  property r4;\n"
      "    q != d1;\n"
      "  endproperty\n"
      "  always @(posedge mclk) begin\n"
      "    #10 q <= d1;\n"
      "    @(negedge mclk)\n"
      "    #10 q1 <= !d1;\n"
      "    r4_p: assert property (r4);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNoClockReport, 10, "16.14.6"));
}

TEST(ProceduralClockInference, AnEdgeWithAnIffIsInferredWhole) {
  ElabFixture f;
  Elaborate(
      "module m(input logic clock, input logic reset, input logic d1);\n"
      "  logic q;\n"
      "  int cnt;\n"
      "  property r2;\n"
      "    q != d1;\n"
      "  endproperty\n"
      "  always_ff @(posedge clock iff reset == 0 or posedge reset) begin\n"
      "    cnt <= reset ? 0 : cnt + 1;\n"
      "    q <= d1;\n"
      "    r2_p: assert property (r2);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(ProceduralClockInference, TheDefaultClockingAndAnOwnClockNeedNoContext) {
  ElabFixture f;
  Elaborate(
      "module m(input logic mclk, input logic scanclk, input logic d1);\n"
      "  logic q, q1;\n"
      "  default clocking dc @(posedge scanclk); endclocking\n"
      "  property r4;\n"
      "    q != d1;\n"
      "  endproperty\n"
      "  always @(posedge mclk) begin\n"
      "    #10 q <= d1;\n"
      "    r4_p: assert property (r4);\n"
      "    r4_own: assert property (@(posedge mclk) r4);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(ProceduralClockInference, AnAutomaticInTheClockingEventIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  logic clks [2];\n"
      "  always @(a) begin\n"
      "    automatic int k = 1;\n"
      "    a1: assert property (@(posedge clks[k]) a);\n"
      "    a2: assert property (@(posedge clks[0]) a);\n"
      "    a3: assert property (@(posedge clks[0] iff k == 1) a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a clocking event of a procedural concurrent "
                            "assertion may not reference an automatic variable",
                            6, "16.14.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a clocking event of a procedural concurrent "
                            "assertion may not reference an automatic variable",
                            8, "16.14.6"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(),
                    "a clocking event of a procedural concurrent "
                    "assertion may not reference an automatic variable",
                    7, "16.14.6"));
}

constexpr const char* kAutomaticClockReport =
    "a clocking event of a procedural concurrent assertion may not reference "
    "an automatic variable";

constexpr const char* kAutomaticDeclarations =
    "  logic clk, a, b;\n"
    "  logic clks [2];\n"
    "  property p(ev); @(ev) a; endproperty\n"
    "  sequence s(ev); @(ev) a; endsequence\n"
    "  property q(ev); @(posedge clk) a ##1 @(ev) b; endproperty\n"
    "  sequence s2(ev); @(ev) b; endsequence\n";

struct AutomaticPlace {
  const char* unit;
  const char* procedure;
};

constexpr AutomaticPlace kAutomaticPlaces[] = {
    {"module", "always @(a)"},
    {"module", "initial"},
    {"module", "always_ff @(posedge clk)"},
    {"interface", "always @(a)"},
    {"program", "initial"}};

std::string AutomaticSource(const AutomaticPlace& place,
                            const std::string& statement) {
  std::string unit = place.unit;
  std::string body = std::string("  ") + place.procedure +
                     " begin\n"
                     "    automatic int k = 1;\n"
                     "    automatic event e2;\n"
                     "    logic st;\n"
                     "    " +
                     statement + "\n  end\n";
  if (unit == "module") {
    return "module t;\n" + std::string(kAutomaticDeclarations) + body +
           "endmodule\n";
  }
  return unit + " w;\n" + kAutomaticDeclarations + body + "end" + unit +
         "\nmodule t;\n  w u();\nendmodule\n";
}

std::string WithDirective(const std::string& statement,
                          const std::string& directive) {
  std::string out = statement;
  out.replace(out.find("assert property"), 15, directive);
  return out;
}

struct AutomaticRow {
  const char* statement;
  bool is_sequence;
};

void ExpectAutomaticClockReported(const AutomaticRow& row) {
  for (const AutomaticPlace& place : kAutomaticPlaces) {
    for (const char* directive : {"assert property", "assume property",
                                  "cover property", "cover sequence"}) {
      if (!row.is_sequence && std::string(directive) == "cover sequence") {
        continue;
      }
      std::string src =
          AutomaticSource(place, WithDirective(row.statement, directive));
      SCOPED_TRACE(src);
      ElabFixture f;
      ElaborateSrcAllowingParseErrors(src, f);
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kAutomaticClockReport,
                                LineHolding(src, "x1:"), "16.14.6"));
    }
  }
}

constexpr AutomaticRow kAutomaticClocksReported[] = {
    {"x1: assert property (@(posedge clks[k]) a);", true},
    {"x1: assert property (@(posedge clks[0] iff k == 1) a);", true},
    {"x1: assert property (@(e2) a);", true},
    {"x1: assert property (p(e2));", false},
    {"x1: assert property (p(posedge clks[k]));", false},
    {"x1: assert property (s(e2));", true}};

constexpr AutomaticRow kLoopVariableClocks[] = {
    {"for (int i = 0; i < 2; i++) x1: assert property (@(posedge clks[i]) a);",
     true},
    {"for (int i = 0; i < 2; i++) "
     "x1: assert property (@(posedge clks[0] iff i == 1) a);",
     true},
    {"foreach (clks[j]) x1: assert property (@(posedge clks[j]) a);", true},
    {"for (int i = 0; i < 2; i++) x1: assert property (p(posedge clks[i]));",
     false}};

constexpr AutomaticRow kAutomaticLaterClocks[] = {
    {"x1: assert property (q(e2));", false},
    {"x1: assert property (@(posedge clk) a ##1 @(posedge clks[k]) b);", true},
    {"x1: assert property (@(posedge clk) a |=> s2(e2));", false}};

constexpr AutomaticRow kStaticClocksAccepted[] = {
    {"x1: assert property (@(st) a);", true},
    {"x1: assert property (@(posedge clk) a && k == 1);", true},
    {"for (int i = 0; i < 2; i++) x1: assert property (@(posedge clk) "
     "clks[i]);",
     true},
    {"x1: assert property (p(posedge clks[0]));", false},
    {"x1: assert property (@(posedge clk) a ##1 @(posedge clks[0]) b);", true}};

TEST(ProceduralClockInference,
     AnAutomaticInALeadingClockIsReportedForEachKindInEachPlace) {
  for (const AutomaticRow& row : kAutomaticClocksReported) {
    ExpectAutomaticClockReported(row);
  }
}

TEST(ProceduralClockInference,
     DISABLED_ALoopVariableInALeadingClockIsReportedForEachKindInEachPlace) {
  for (const AutomaticRow& row : kLoopVariableClocks) {
    ExpectAutomaticClockReported(row);
  }
}

TEST(ProceduralClockInference,
     DISABLED_AnAutomaticInALaterClockIsReportedForEachKindInEachPlace) {
  for (const AutomaticRow& row : kAutomaticLaterClocks) {
    ExpectAutomaticClockReported(row);
  }
}

TEST(ProceduralClockInference,
     AStaticClockAndAnAutomaticOutsideTheClockAreAcceptedInEachPlace) {
  for (const AutomaticRow& row : kStaticClocksAccepted) {
    for (const AutomaticPlace& place : kAutomaticPlaces) {
      std::string src = AutomaticSource(place, row.statement);
      SCOPED_TRACE(src);
      ElabFixture f;
      ElaborateSrc(src, f);
      EXPECT_FALSE(f.has_errors);
    }
  }
}

TEST(ProceduralClockInference, AGenvarInTheClockIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic a;\n"
      "  logic clks [2];\n"
      "  for (genvar g = 0; g < 2; g++) begin : gl\n"
      "    always @(a) x1: assert property (@(posedge clks[g]) a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

constexpr const char* kInferenceDeclarations =
    "  logic clk, clk2, a, b, q, d;\n"
    "  event ev;\n"
    "  clocking cb @(posedge clk); input b; output d; endclocking\n";

constexpr const char* kInferenceDefault =
    "  default clocking dc @(posedge clk2); endclocking\n";

std::string InferenceSource(const std::string& unit,
                            const std::string& procedure,
                            const std::string& declarations) {
  std::string body = std::string(kInferenceDeclarations) + declarations + "  " +
                     procedure + "\n";
  if (unit == "module") return "module t;\n" + body + "endmodule\n";
  if (unit == "generate") {
    return "module t;\n  if (1) begin : g\n" + body + "  end\nendmodule\n";
  }
  return unit + " w;\n" + body + "end" + unit +
         "\nmodule t;\n  w u();\nendmodule\n";
}

std::string AsAssume(const std::string& procedure) {
  std::string out = procedure;
  out.replace(out.find("x1: assert property"), 19, "x1: assume property");
  return out;
}

constexpr const char* kNoClockProcedures[] = {
    "always @(posedge clk) begin #1; x1: assert property (a); end",
    "always @(posedge clk) begin wait (b); x1: assert property (a); end",
    "always @(posedge clk) begin wait fork; x1: assert property (a); end",
    "always @(posedge clk) begin @(negedge clk); x1: assert property (a); end",
    "always_comb begin q = d; x1: assert property (a); end",
    "always_latch begin if (b) q = d; x1: assert property (a); end",
    "always @* begin q = d; x1: assert property (a); end",
    "initial begin x1: assert property (a); end",
    "always @(clk) begin x1: assert property (a); end",
    "always @(posedge clk or posedge clk2) begin x1: assert property (a); end",
    "always @(posedge clk, posedge clk2) begin x1: assert property (a); end",
    "always @(ev or posedge clk2) begin x1: assert property (a); end",
    "always @(cb or cb) begin x1: assert property (a); end",
    "always @(posedge (clk & b)) begin q = b; x1: assert property (a); end",
    "always @(posedge clk) begin q = clk; x1: assert property (a); end",
    "always @(ev) begin -> ev; x1: assert property (a); end",
    "always @(ev) begin q = ev.triggered; x1: assert property (a); end",
    "always @(cb) begin @(cb); x1: assert property (a); end"};

constexpr const char* kIntraAssignmentControlProcedures[] = {
    "always @(posedge clk) begin q = #1 d; x1: assert property (a); end",
    "always @(posedge clk) begin q = @(posedge clk2) d; "
    "x1: assert property (a); end",
    "always @(posedge clk) begin q = repeat (2) @(posedge clk2) d; "
    "x1: assert property (a); end",
    "always @(posedge clk) begin q <= @(posedge clk2) d; "
    "x1: assert property (a); end"};

constexpr const char* kInferredProcedures[] = {
    "always @(posedge clk) begin q <= #1 d; x1: assert property (a); end",
    "initial begin @(posedge clk); x1: assert property (a); end",
    "always @(edge clk) begin x1: assert property (a); end",
    "always @(posedge (clk & b)) begin x1: assert property (a); end",
    "always @(ev) begin x1: assert property (a); end",
    "always @(cb) begin x1: assert property (a); end",
    "always @(ev or posedge clk2) begin q = clk2; x1: assert property (a); end",
    "always @(posedge clk iff b) begin q = b; x1: assert property (a); end",
    "always @(posedge clk) begin assert (clk); x1: assert property (clk); end",
    "always @(posedge clk) begin q <= $rose(a, @(posedge clk)); "
    "x1: assert property (a); end",
    "always @(ev) begin x2: assert property (@(ev) b); "
    "x1: assert property (a); end",
    "always @(posedge clk) begin x2: assert property (@(posedge clk) b); "
    "x1: assert property (a); end"};

constexpr const char* kClockingBlockSignalProcedures[] = {
    "always @(cb) begin q = cb.b; x1: assert property (a); end",
    "always @(cb) begin cb.d <= a; x1: assert property (a); end"};

void ExpectNoClockReported(const std::string& unit,
                           const std::string& procedure) {
  for (const std::string& form : {procedure, AsAssume(procedure)}) {
    std::string src = InferenceSource(unit, form, "");
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoClockReport,
                              LineHolding(src, "x1:"), "16.14.6"));
  }
}

void ExpectClockFound(const std::string& unit, const std::string& procedure,
                      const std::string& declarations) {
  for (const std::string& form : {procedure, AsAssume(procedure)}) {
    std::string src = InferenceSource(unit, form, declarations);
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_FALSE(f.has_errors);
  }
}

TEST(ProceduralClockInference, EachFormThatInfersNoClockIsReported) {
  for (const char* procedure : kNoClockProcedures) {
    ExpectNoClockReported("module", procedure);
  }
}

TEST(ProceduralClockInference,
     DISABLED_AnIntraAssignmentTimingControlInfersNoClock) {
  for (const char* procedure : kIntraAssignmentControlProcedures) {
    ExpectNoClockReported("module", procedure);
  }
}

TEST(ProceduralClockInference,
     EachFormThatInfersNoClockTakesTheDefaultClockingWithoutAReport) {
  for (const char* procedure : kNoClockProcedures) {
    ExpectClockFound("module", procedure, kInferenceDefault);
  }
  for (const char* procedure : kIntraAssignmentControlProcedures) {
    ExpectClockFound("module", procedure, kInferenceDefault);
  }
}

TEST(ProceduralClockInference, EachFormThatInfersAClockIsAccepted) {
  for (const char* procedure : kInferredProcedures) {
    ExpectClockFound("module", procedure, "");
  }
}

TEST(ProceduralClockInference,
     DISABLED_AClockingBlockWhoseSignalTheProcedureUsesIsInferred) {
  for (const char* procedure : kClockingBlockSignalProcedures) {
    ExpectClockFound("module", procedure, "");
    ExpectClockFound("interface", procedure, "");
  }
}

constexpr const char* kInferenceUnits[] = {"interface", "generate"};

TEST(ProceduralClockInference, InferenceHoldsInAnInterfaceAndAGenerateBlock) {
  for (const char* unit : kInferenceUnits) {
    ExpectNoClockReported(unit, kNoClockProcedures[0]);
    ExpectNoClockReported(unit, kNoClockProcedures[9]);
    ExpectClockFound(unit, kInferredProcedures[0], "");
    ExpectClockFound(unit, kInferredProcedures[5], "");
  }
}

TEST(ProceduralClockInference, InferenceHoldsInAProgramAndAChecker) {
  ExpectNoClockReported("program",
                        "initial begin x1: assert property (a); end");
  ExpectClockFound("program",
                   "initial begin @(posedge clk); x1: assert property (a); end",
                   "");
  ExpectClockFound(
      "checker", "always_ff @(posedge clk) begin x1: assert property (a); end",
      "");
  ExpectNoClockReported("checker",
                        "initial begin x1: assert property (a); end");
}

}  // namespace
