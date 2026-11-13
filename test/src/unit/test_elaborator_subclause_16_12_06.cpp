#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
#include <string>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kConditionReport =
    "a sequence stands where the grammar admits only an expression_or_dist";

constexpr const char* kConditionDeclarations =
    "  sequence s; a ##1 b; endsequence\n"
    "  sequence sa(x, y); x ##1 y; endsequence\n"
    "  property p; a |-> b; endproperty\n";

std::string Replace(std::string text, const std::string& from,
                    const std::string& to) {
  for (size_t at = text.find(from); at != std::string::npos;
       at = text.find(from, at + to.size())) {
    text.replace(at, from.size(), to);
  }
  return text;
}

std::string ConditionIn(const std::string& place, const std::string& body) {
  std::string assertion =
      "  a1: assert property (@(posedge clk) " + body + ");\n";
  std::string signals = "  logic clk; bit a, b, c;\n";
  if (place == "module") {
    return "module m;\n" + signals + kConditionDeclarations + assertion +
           "endmodule\n";
  }
  if (place == "procedural") {
    return "module m;\n" + signals + kConditionDeclarations +
           "  always @(posedge clk) a1: assert property (" + body +
           ");\nendmodule\n";
  }
  if (place == "generate") {
    return "module m;\n" + signals + "  if (1) begin : g\n" +
           kConditionDeclarations + assertion + "  end\nendmodule\n";
  }
  if (place == "interface" || place == "program") {
    return place + " m;\n" + signals + kConditionDeclarations + assertion +
           "end" + place + "\n";
  }
  if (place == "checker") {
    return "checker m;\n" + signals + kConditionDeclarations + assertion +
           "endchecker\n";
  }
  if (place == "unit") {
    return "logic clk; bit a, b, c;\n" +
           Replace(kConditionDeclarations, "  ", "") +
           "property outer; @(posedge clk) " + body +
           "; endproperty\nmodule m; endmodule\n";
  }
  if (place == "package name") {
    return "package pk;\n" + std::string(kConditionDeclarations) +
           "  bit a, b;\nendpackage\nmodule m;\n  logic clk; bit a, b, c;\n"
           "  a1: assert property (@(posedge clk) " +
           Replace(Replace(body, "(s", "(pk::s"), "(p)", "(pk::p)") +
           ");\nendmodule\n";
  }
  return "package pk;\n" + signals + kConditionDeclarations +
         "  property outer; @(posedge clk) " + body +
         "; endproperty\nendpackage\nmodule m; endmodule\n";
}

int ConditionLine(const std::string& place) {
  if (place == "generate" || place == "package name") return 7;
  if (place == "unit") return 5;
  return 6;
}

constexpr const char* kConditionPlaces[] = {
    "module",  "procedural", "generate", "interface",
    "program", "checker",    "package"};

const char* const kSequenceOrPropertyConditions[] = {
    "if (s) c", "if (s) c else a", "if (sa(a, b)) c", "if (p) c",
    "if (p) c else a"};

const char* const kExpressionConditions[] = {"if (s.triggered) c", "if (a) c",
                                             "if (a && !b) c else a",
                                             "if (a dist {1 := 1}) c else b"};

TEST(PropertyIfElse,
     DISABLED_ASequenceOrPropertyAsTheConditionIsReportedInEachPlace) {
  std::vector<std::string> places(std::begin(kConditionPlaces),
                                  std::end(kConditionPlaces));
  places.emplace_back("unit");
  places.emplace_back("package name");
  for (const std::string& place : places) {
    for (const char* body : kSequenceOrPropertyConditions) {
      SCOPED_TRACE(place + " " + body);
      ElabFixture f;
      ElaborateSrc(ConditionIn(place, body), f);
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kConditionReport,
                                ConditionLine(place), "A.2.10"));
    }
  }
}

TEST(PropertyIfElse, AnExpressionAsTheConditionIsAcceptedInEachPlace) {
  for (const char* place : kConditionPlaces) {
    for (const char* body : kExpressionConditions) {
      SCOPED_TRACE(std::string(place) + " " + body);
      ElabFixture f;
      ElaborateSrc(ConditionIn(place, body), f);
      EXPECT_FALSE(f.diag.HasErrors());
    }
  }
}

}  // namespace
