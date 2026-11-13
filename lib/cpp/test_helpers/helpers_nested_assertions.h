#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

inline constexpr const char* kNestedConcurrent[] = {
    "assert property (@(posedge clk) b);",
    "assume property (@(posedge clk) b);", "cover property (@(posedge clk) b);",
    "cover sequence (@(posedge clk) b);"};

inline constexpr const char* kNestedImmediate[] = {
    "assert (b);",       "assume (b);",       "cover (b);",
    "assert #0 (b);",    "assume #0 (b);",    "cover #0 (b);",
    "assert final (b);", "assume final (b);", "cover final (b);"};

inline constexpr const char* kNestingDepths[] = {
    "begin % end",           "if (b) %",
    "if (b) ; else %",       "for (int i = 0; i < 2; i++) %",
    "fork % join",           "case (b) 1'b1: % endcase",
    "assert (b) else %",     "assert (b) %",
    "randcase 1: % endcase", "randsequence (m) m: { % }; endsequence"};

inline constexpr const char* kNestingProcedures[] = {
    "always @(posedge clk) ", "initial ", "always_ff @(posedge clk) ",
    "always_comb ", "always_latch "};

inline constexpr const char* kNestingDesignUnits[] = {"interface", "program",
                                                      "checker"};

inline constexpr const char* kNestingGenerateBlocks[] = {"if generate",
                                                         "for generate"};

inline constexpr const char* kNestingPlaces[] = {
    "module", "interface", "program", "checker", "if generate", "for generate"};

inline std::string NestingWrapped(std::string_view depth,
                                  std::string_view nested) {
  std::string out(depth);
  out.replace(out.find('%'), 1, nested);
  return out;
}

inline std::string NestingProcedureIn(std::string_view place) {
  if (place == "program") return "initial ";
  if (place == "checker") return "always_ff @(posedge clk) ";
  return "always @(posedge clk) ";
}

inline std::string NestingSource(const std::string& place,
                                 const std::string& item) {
  std::string line = "  " + item + "\n";
  std::string top_signals = "  logic clk, a, b;\n";
  if (place == "module") {
    return "module t;\n" + top_signals + line + "endmodule\n";
  }
  if (place == "if generate") {
    return "module t;\n" + top_signals + "  if (1) begin : g\n" + line +
           "  end\nendmodule\n";
  }
  if (place == "for generate") {
    return "module t;\n" + top_signals +
           "  for (genvar i = 0; i < 2; i++) begin : gl\n" + line +
           "  end\nendmodule\n";
  }
  std::string header = place == "checker"
                           ? "checker w(clk, a, b);\n"
                           : place + " w(input logic clk, a, b);\n";
  return header + line + "end" + place + "\nmodule t;\n" + top_signals +
         "  w u(clk, a, b);\nendmodule\n";
}

inline ::testing::AssertionResult NestingReportedAlone(
    const std::string& src, std::string_view report,
    std::string_view subclause) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(src, f);
  const std::vector<Diagnostic>& diags = f.diag.Diagnostics();
  for (const Diagnostic& diag : diags) {
    if (diag.message.find("always or an initial procedure") !=
        std::string::npos) {
      return ::testing::AssertionFailure()
             << "the placement rule was reported beside the nesting rule:\n"
             << src;
    }
  }
  ::testing::AssertionResult reported =
      ReportedError(diags, report, LineHolding(src, "x1:"), subclause);
  if (!reported) reported << "\nin\n" << src;
  return reported;
}

inline ::testing::AssertionResult NestingAccepted(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  if (f.has_errors) {
    return ::testing::AssertionFailure() << "a report met\n" << src;
  }
  return ::testing::AssertionSuccess();
}

template <size_t N>
std::vector<std::string> NestingForms(const std::vector<std::string>& outers,
                                      const char* const (&nested_list)[N]) {
  std::vector<std::string> forms;
  for (const std::string& outer : outers) {
    for (const char* nested : nested_list) forms.push_back(outer + nested);
  }
  return forms;
}

inline std::vector<std::string> NestingDepthForms(
    const std::vector<std::string>& outers) {
  std::vector<std::string> forms;
  for (const char* depth : kNestingDepths) {
    for (const std::string& outer : outers) {
      for (const char* nested : kNestedConcurrent) {
        forms.push_back(outer + NestingWrapped(depth, nested));
      }
    }
  }
  return forms;
}

template <size_t N>
void ExpectNestingReportedIn(const char* const (&places)[N],
                             const std::vector<std::string>& forms,
                             bool procedural, std::string_view report,
                             std::string_view subclause) {
  for (const char* place : places) {
    std::string procedure = procedural ? NestingProcedureIn(place) : "";
    for (const std::string& form : forms) {
      EXPECT_TRUE(NestingReportedAlone(NestingSource(place, procedure + form),
                                       report, subclause));
    }
  }
}

inline void ExpectNestingAcceptedEverywhere(
    const std::vector<std::string>& forms) {
  for (const char* place : kNestingPlaces) {
    std::string procedure = NestingProcedureIn(place);
    for (const std::string& form : forms) {
      EXPECT_TRUE(NestingAccepted(NestingSource(place, procedure + form)));
      EXPECT_TRUE(NestingAccepted(NestingSource(place, form)));
    }
  }
}

inline void ExpectNestingReportedInEachProcedure(
    const std::vector<std::string>& forms, std::string_view report,
    std::string_view subclause) {
  for (const char* procedure : kNestingProcedures) {
    bool allows_fork = !std::string_view(procedure).starts_with("always_");
    for (const std::string& form : forms) {
      if (!allows_fork && form.find("fork") != std::string::npos) continue;
      EXPECT_TRUE(NestingReportedAlone(
          NestingSource("module", procedure + form), report, subclause));
    }
  }
}
