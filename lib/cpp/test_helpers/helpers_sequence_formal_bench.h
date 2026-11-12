#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

inline std::string FormalBench(const std::string& items,
                               const std::string& outside = "") {
  return outside +
         "module top;\n"
         "  logic clk = 0, a = 1, b = 1, c = 1;\n"
         "  " +
         items + "\nendmodule\n";
}

inline std::string FilledForm(std::string src, std::string_view form) {
  for (std::size_t at = src.find("@@"); at != std::string::npos;
       at = src.find("@@", at + form.size())) {
    src.replace(at, 2, form);
  }
  return src;
}

inline int FormalReportsAt(const std::vector<Diagnostic>& diags,
                           std::string_view message, uint32_t line) {
  int count = 0;
  for (const auto& diag : diags) {
    if (diag.severity == DiagSeverity::kError && diag.loc.line == line &&
        diag.subclause == "16.8.1" &&
        diag.message.find(message) != std::string::npos) {
      ++count;
    }
  }
  return count;
}

inline void ExpectFormAccepted(const std::string& marked,
                               std::string_view form) {
  const std::string kSrc = FilledForm(marked, form);
  ElabFixture f;
  auto* design = ElaborateSrc(kSrc, f);
  ASSERT_NE(design, nullptr) << kSrc;
  EXPECT_FALSE(f.has_errors) << kSrc;
}

inline void ExpectFormReported(const std::string& marked, std::string_view form,
                               std::string_view message,
                               std::string_view at = "@@", int times = 1) {
  const std::string kSrc = FilledForm(marked, form);
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(kSrc, f);
  EXPECT_EQ(
      FormalReportsAt(f.diag.Diagnostics(), message, LineHolding(marked, at)),
      times)
      << kSrc;
}

struct PlacedSource {
  std::string place;
  std::string source;
};

inline bool InAModuleOrUnit(const PlacedSource& placed) {
  return placed.place == "module" || placed.place == "interface" ||
         placed.place == "program" || placed.place == "checker";
}

inline std::string InUnit(const char* kind, const std::string& body) {
  const std::string kKind = kind;
  const std::string kPorts = kKind == "checker"
                                 ? "(logic clk, logic a, logic b, logic c)"
                                 : "(input logic clk, a, b, c)";
  return kKind + " u_unit" + kPorts + ";\n  " + body + "\nend" + kKind + "\n";
}

inline std::vector<PlacedSource> InEveryDeclarationPlace(
    const std::string& decl, const std::string& use) {
  const std::string kBody = decl + "\n  " + use;
  std::vector<PlacedSource> out;
  out.push_back({"module", FormalBench(kBody)});
  for (const char* kind : {"interface", "program", "checker"}) {
    out.push_back(
        {kind, FormalBench("u_unit u(clk, a, b, c);", InUnit(kind, kBody))});
  }
  out.push_back({"package", FormalBench("import pk::*;\n  " + use,
                                        "package pk;\n  bit clk, a, b, c;\n  " +
                                            decl + "\nendpackage\n")});
  out.push_back({"compilation unit",
                 FormalBench(use, "bit clk, a, b, c;\n" + decl + "\n")});
  out.push_back({"conditional generate",
                 FormalBench("if (1) begin : g\n    " + kBody + "\n  end")});
  out.push_back({"loop generate",
                 FormalBench("for (genvar i = 0; i < 1; i++) begin : lg\n    " +
                             kBody + "\n  end")});
  out.push_back(
      {"case generate", FormalBench("case (1)\n    1: begin : cg\n      " +
                                    kBody + "\n    end\n  endcase")});
  out.push_back({"nested generate",
                 FormalBench("if (1) begin : g1\n    if (1) begin : g2\n"
                             "      " +
                             kBody + "\n    end\n  end")});
  if (use.empty()) {
    out.push_back(
        {"clocking block", FormalBench("clocking cb @(posedge clk);\n    " +
                                       decl + "\n  endclocking")});
  }
  return out;
}
