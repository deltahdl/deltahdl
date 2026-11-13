#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kPropertyForSequence =
    "a property stands where the grammar admits only a sequence";

constexpr const char* kNamedDeclarations =
    "  sequence s; a ##1 b; endsequence\n"
    "  sequence sa(x, y); x ##1 y; endsequence\n"
    "  property p; a |-> b; endproperty\n"
    "  property pa(x, y); x |=> y; endproperty\n"
    "  property pb; a ##1 b; endproperty\n";

std::string NamedIn(const std::string& place, const std::string& spec) {
  const std::string kSignals = "  logic clk; bit a, b, c;\n";
  const std::string kAssertion =
      "  a1: assert property (@(posedge clk) " + spec + ");\n";
  if (place == "procedural") {
    return "module m;\n" + kSignals + kNamedDeclarations +
           "  always @(posedge clk) a1: assert property (" + spec +
           ");\nendmodule\n";
  }
  if (place == "generate") {
    return "module m;\n" + kSignals + "  if (1) begin : g\n" +
           kNamedDeclarations + kAssertion + "  end\nendmodule\n";
  }
  if (place == "interface" || place == "program" || place == "checker") {
    return place + " m;\n" + kSignals + kNamedDeclarations + kAssertion +
           "end" + place + "\n";
  }
  const std::string kOuter =
      "  property outer; @(posedge clk) " + spec + "; endproperty\n";
  if (place == "package property") {
    return "package pk;\n" + kSignals + kNamedDeclarations + kOuter +
           "endpackage\nmodule m; endmodule\n";
  }
  if (place == "unit property") {
    return kSignals + kNamedDeclarations + kOuter + "module m; endmodule\n";
  }
  if (place == "package name") {
    return "package pk;\n  bit a, b;\n" + std::string(kNamedDeclarations) +
           "endpackage\nmodule m;\n" + kSignals + kAssertion + "endmodule\n";
  }
  return "module m;\n" + kSignals + kNamedDeclarations + kAssertion +
         "endmodule\n";
}

int NamedLine(const std::string& place) {
  if (place == "generate") return 9;
  if (place == "unit property") return 7;
  if (place == "package name") return 11;
  return 8;
}

constexpr const char* kNamedPlaces[] = {
    "module",  "procedural", "generate",         "interface",
    "program", "checker",    "package property", "unit property"};

TEST(ImplicationAntecedent,
     DISABLED_ANamedPropertyAsTheAntecedentIsReportedInEachPlace) {
  for (const char* place : kNamedPlaces) {
    for (const char* spec :
         {"p |-> c", "p |=> c", "pa(a, b) |-> c", "pb |=> c", "(pb) |-> c"}) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      ElabFixture f;
      ElaborateSrc(NamedIn(place, spec), f);
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kPropertyForSequence,
                                NamedLine(place), "A.2.10"));
    }
  }
  for (const char* spec : {"pk::p |-> c", "pk::pb |=> c"}) {
    SCOPED_TRACE(spec);
    ElabFixture f;
    ElaborateSrc(NamedIn("package name", spec), f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kPropertyForSequence,
                              NamedLine("package name"), "A.2.10"));
  }
}

TEST(ImplicationAntecedent,
     ANamedSequenceAsTheAntecedentIsAcceptedInEachPlace) {
  for (const char* place : kNamedPlaces) {
    for (const char* spec :
         {"s |-> c", "s |=> c", "sa(a, b) |-> c", "(s) |=> c", "a |-> p",
          "s |=> pa(a, b)", "sa(a, b) ##1 s |-> pb"}) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      ElabFixture f;
      ElaborateSrc(NamedIn(place, spec), f);
      EXPECT_FALSE(f.diag.HasErrors());
    }
  }
  for (const char* spec : {"pk::s |-> c", "a |=> pk::p"}) {
    SCOPED_TRACE(spec);
    ElabFixture f;
    ElaborateSrc(NamedIn("package name", spec), f);
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

}  // namespace
