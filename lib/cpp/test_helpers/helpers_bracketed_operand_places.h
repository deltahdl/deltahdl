#pragma once

#include <gtest/gtest.h>

#include <cctype>
#include <cstddef>
#include <initializer_list>
#include <string>
#include <vector>

#include "fixture_elaborator.h"
#include "fixture_parser.h"
#include "helpers_reported_error.h"

constexpr const char* kOperandDeclarations =
    "  bit clk, a;\n"
    "  int k;\n"
    "  localparam int NEG = -1, ONE = 1, LO = 4, HI = 2;\n"
    "  localparam real R = 1.5; localparam shortreal S = 2.5;\n";

constexpr int kOperandLine = 6;

inline std::string BracketedStatement(const std::string& op,
                                      const std::string& operand) {
  return "a1: assert property (@(posedge clk) " + op + " [" + operand + "] a);";
}

inline std::string BracketedDeclaration(const std::string& op,
                                        const std::string& operand) {
  return "property q; @(posedge clk) " + op + " [" + operand +
         "] a; endproperty";
}

inline std::string OperandIn(const std::string& place,
                             const std::string& target) {
  const std::string kBody = kOperandDeclarations + ("  " + target + "\n");
  if (place == "checker") {
    return "checker m;\n  bit clk, a;\n  int k;\n  bit x;\n  bit y;\n  " +
           target + "\nendchecker\n";
  }
  if (place == "interface" || place == "program") {
    return place + " m;\n" + kBody + "end" + place + "\n";
  }
  if (place == "if generate") {
    return "module m;\n" + std::string(kOperandDeclarations) +
           "  if (1) begin : g " + target + " end\nendmodule\n";
  }
  if (place == "for generate") {
    return "module m;\n" + std::string(kOperandDeclarations) +
           "  for (genvar i = 0; i < 1; i++) begin : g " + target +
           " end\nendmodule\n";
  }
  if (place == "package") {
    return "package pk;\n" + kBody + "endpackage\nmodule m; endmodule\n";
  }
  if (place == "used package") {
    return "package pk;\n" + kBody +
           "endpackage\nmodule m;\n  bit clk;\n"
           "  a2: assert property (pk::q);\nendmodule\n";
  }
  if (place == "unit") return "\n" + kBody + "module m; endmodule\n";
  return "module m;\n" + kBody + "endmodule\n";
}

constexpr const char* kOperandStatementPlaces[] = {
    "module", "interface", "program", "checker", "if generate", "for generate"};

constexpr const char* kOperandDeclarationPlaces[] = {
    "module",       "interface", "program",      "checker", "if generate",
    "for generate", "package",   "used package", "unit"};

inline bool NeedsAParameter(const std::string& place,
                            const std::string& operand) {
  if (place != "checker") return false;
  for (char ch : operand) {
    if (std::isupper(static_cast<unsigned char>(ch)) != 0) return true;
  }
  return false;
}

inline void ExpectOperandReported(const std::string& src, const char* report,
                                  const char* subclause,
                                  int line = kOperandLine) {
  auto parsed = Parse(src);
  if (parsed.has_errors) {
    EXPECT_TRUE(ReportedError(parsed.diags, report, line, subclause));
    return;
  }
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), report, line, subclause));
}

inline void ExpectOperandAccepted(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
}

using OperandTarget = std::string (*)(const std::string&, const std::string&);

template <size_t Places, size_t Operands, typename Expect>
void ForEachOperand(const char* const (&places)[Places],
                    std::initializer_list<const char*> ops,
                    const char* const (&operands)[Operands],
                    OperandTarget target, Expect expect) {
  for (const char* place : places) {
    for (const char* op : ops) {
      for (const char* operand : operands) {
        if (NeedsAParameter(place, operand)) continue;
        SCOPED_TRACE(std::string(place) + " " + op + " " + operand);
        expect(OperandIn(place, target(op, operand)));
      }
    }
  }
}

inline std::vector<std::string> OperandDirectives(const std::string& spec) {
  return {"a1: assume property (@(posedge clk) " + spec + ");",
          "a1: cover property (@(posedge clk) " + spec + ");",
          "initial a1: assert property (@(posedge clk) " + spec + ");",
          "always @(posedge clk) a1: assert property (" + spec + ");",
          "initial expect (@(posedge clk) " + spec + ");"};
}

inline std::string FormalOperandSource(const std::string& formals,
                                       const std::string& operation,
                                       const std::string& actuals) {
  return "module m;\n" + std::string(kOperandDeclarations) + "  property q(" +
         formals + "); @(posedge clk) " + operation +
         " a; endproperty\n"
         "  a1: assert property (q(" +
         actuals + "));\nendmodule\n";
}

using SourceExpectation = void (*)(const std::string&);

inline void ExpectInEachPlace(const std::string& spec,
                              SourceExpectation expect) {
  for (const char* place : kOperandStatementPlaces) {
    SCOPED_TRACE(std::string(place) + " statement " + spec);
    expect(
        OperandIn(place, "a1: assert property (@(posedge clk) " + spec + ");"));
  }
  for (const char* place : kOperandDeclarationPlaces) {
    SCOPED_TRACE(std::string(place) + " declaration " + spec);
    expect(OperandIn(place,
                     "property q; @(posedge clk) " + spec + "; endproperty"));
  }
}

inline void ExpectGrammarReported(const std::string& src) {
  ExpectOperandReported(src, "the grammar admits", "A.2.10");
}
