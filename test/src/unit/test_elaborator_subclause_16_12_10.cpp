#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "elaborator/nexttime_index.h"
#include "fixture_elaborator.h"
#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(NexttimeIndex, NonNegativeConstantIsWellFormed) {
  EXPECT_TRUE(IsNexttimeIndexWellFormed(MakeNexttimeIndex(0)));
  EXPECT_TRUE(IsNexttimeIndexWellFormed(MakeNexttimeIndex(1)));
  EXPECT_TRUE(IsNexttimeIndexWellFormed(MakeNexttimeIndex(7)));
}

TEST(NexttimeIndex, NegativeConstantIsRejected) {
  EXPECT_FALSE(IsNexttimeIndexWellFormed(MakeNexttimeIndex(-1)));
}

TEST(NexttimeIndex, NonConstantIsRejected) {
  NexttimeIndex index;
  index.is_constant = false;
  index.is_integer = true;
  index.value = 2;
  EXPECT_FALSE(IsNexttimeIndexWellFormed(index));
}

TEST(NexttimeIndex, NonIntegerConstantIsRejected) {
  NexttimeIndex index;
  index.is_constant = true;
  index.is_integer = false;
  index.value = 0;
  EXPECT_FALSE(IsNexttimeIndexWellFormed(index));
}

TEST(NexttimeIndexElaboration, AParameterIndexIsChecked) {
  const char* const kReport =
      "the index of nexttime shall be a non-negative integer constant "
      "expression";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  int k;\n"
      "  localparam int NEG = -1, ONE = 1;\n"
      "  a1: assert property (@(posedge clk) nexttime [NEG] a);\n"
      "  a2: assert property (@(posedge clk) s_nexttime [k] a);\n"
      "  a3: assert property (@(posedge clk) nexttime [ONE] a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 5, "16.12.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 6, "16.12.10"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 7, "16.12.10"));
}

constexpr const char* kIndexReport = "non-negative integer constant";

constexpr const char* kIndexDeclarations =
    "  bit clk, a;\n"
    "  int k;\n"
    "  localparam int NEG = -1, ONE = 1;\n"
    "  localparam real R = 1.5;\n";

std::string IndexedStatement(const std::string& op, const std::string& index) {
  return "a1: assert property (@(posedge clk) " + op + " [" + index + "] a);";
}

std::string IndexedDeclaration(const std::string& op,
                               const std::string& index) {
  return "property q; @(posedge clk) " + op + " [" + index + "] a; endproperty";
}

std::string IndexIn(const std::string& place, const std::string& target) {
  const std::string kBody = kIndexDeclarations + ("  " + target + "\n");
  if (place == "checker") {
    return "checker m;\n  bit clk, a;\n  int k;\n  bit x;\n  bit y;\n  " +
           target + "\nendchecker\n";
  }
  if (place == "interface" || place == "program") {
    return place + " m;\n" + kBody + "end" + place + "\n";
  }
  if (place == "if generate") {
    return "module m;\n" + std::string(kIndexDeclarations) +
           "  if (1) begin : g " + target + " end\nendmodule\n";
  }
  if (place == "for generate") {
    return "module m;\n" + std::string(kIndexDeclarations) +
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

constexpr const char* kStatementPlaces[] = {
    "module", "interface", "program", "checker", "if generate", "for generate"};

constexpr const char* kDeclarationPlaces[] = {
    "module",       "interface", "program",      "checker", "if generate",
    "for generate", "package",   "used package", "unit"};

constexpr const char* kForbiddenIndices[] = {"-1", "(-1)", "NEG",
                                             "k",  "1.5",  "R"};

constexpr const char* kAllowedIndices[] = {"0",       "1",         "ONE",
                                           "int'(R)", "$clog2(4)", "(2)"};

bool NeedsAParameter(const std::string& place, const std::string& index) {
  return place == "checker" && (index.find("NEG") != std::string::npos ||
                                index.find("ONE") != std::string::npos ||
                                index.find('R') != std::string::npos);
}

void ExpectIndexReported(const std::string& src) {
  auto parsed = Parse(src);
  if (parsed.has_errors) {
    EXPECT_TRUE(ReportedError(parsed.diags, kIndexReport, 6, "16.12.10"));
    return;
  }
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kIndexReport, 6, "16.12.10"));
}

void ExpectIndexAccepted(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
}

using IndexedTarget = std::string (*)(const std::string&, const std::string&);
using IndexExpectation = void (*)(const std::string&);

template <size_t Places, size_t Indices>
void ExpectEachIndex(const char* const (&places)[Places],
                     const char* const (&indices)[Indices],
                     IndexedTarget target, IndexExpectation expect) {
  for (const char* place : places) {
    for (const char* op : {"nexttime", "s_nexttime"}) {
      for (const char* index : indices) {
        if (NeedsAParameter(place, index)) continue;
        SCOPED_TRACE(std::string(place) + " " + op + " " + index);
        expect(IndexIn(place, target(op, index)));
      }
    }
  }
}

TEST(NexttimeIndexElaboration,
     DISABLED_ABadIndexInAnAssertionStatementIsReportedInEachPlace) {
  ExpectEachIndex(kStatementPlaces, kForbiddenIndices, IndexedStatement,
                  ExpectIndexReported);
}

TEST(NexttimeIndexElaboration,
     DISABLED_ABadIndexInAPropertyDeclarationIsReportedInEachPlace) {
  ExpectEachIndex(kDeclarationPlaces, kForbiddenIndices, IndexedDeclaration,
                  ExpectIndexReported);
}

TEST(NexttimeIndexElaboration, AGoodIndexIsAcceptedInEachPlace) {
  ExpectEachIndex(kStatementPlaces, kAllowedIndices, IndexedStatement,
                  ExpectIndexAccepted);
  ExpectEachIndex(kDeclarationPlaces, kAllowedIndices, IndexedDeclaration,
                  ExpectIndexAccepted);
}

TEST(NexttimeIndexElaboration,
     DISABLED_ANegativeLiteralIndexIsReportedInEveryDirective) {
  for (const char* op : {"nexttime", "s_nexttime"}) {
    for (const char* index : {"-1", "(-1)"}) {
      const std::string kIndexed = std::string(op) + " [" + index + "] a";
      for (const std::string& target :
           {"a1: assume property (@(posedge clk) " + kIndexed + ");",
            "a1: cover property (@(posedge clk) " + kIndexed + ");",
            "initial a1: assert property (@(posedge clk) " + kIndexed + ");",
            "always @(posedge clk) a1: assert property (" + kIndexed + ");",
            "initial expect (@(posedge clk) " + kIndexed + ");"}) {
        SCOPED_TRACE(target);
        ExpectIndexReported(IndexIn("module", target));
      }
    }
  }
}

TEST(NexttimeIndexElaboration, AGoodIndexIsAcceptedInEveryDirective) {
  for (const char* op : {"nexttime", "s_nexttime"}) {
    const std::string kIndexed = std::string(op) + " [1] a";
    for (const std::string& target :
         {"a1: assume property (@(posedge clk) " + kIndexed + ");",
          "a1: cover property (@(posedge clk) " + kIndexed + ");",
          "initial a1: assert property (@(posedge clk) " + kIndexed + ");",
          "always @(posedge clk) a1: assert property (" + kIndexed + ");",
          "initial expect (@(posedge clk) " + kIndexed + ");"}) {
      SCOPED_TRACE(target);
      ExpectIndexAccepted(IndexIn("module", target));
    }
  }
}

std::string FormalIndexSource(const std::string& op,
                              const std::string& actual) {
  return "module m;\n" + std::string(kIndexDeclarations) +
         "  property q(n); @(posedge clk) " + op +
         " [n] a; endproperty\n"
         "  a1: assert property (q(" +
         actual + "));\nendmodule\n";
}

TEST(NexttimeIndexElaboration, DISABLED_ABadActualForAFormalIndexIsReported) {
  for (const char* op : {"nexttime", "s_nexttime"}) {
    for (const char* actual : {"-1", "NEG", "k", "1.5", "R"}) {
      SCOPED_TRACE(std::string(op) + " " + actual);
      ElabFixture f;
      ElaborateSrc(FormalIndexSource(op, actual), f);
      EXPECT_TRUE(
          ReportedError(f.diag.Diagnostics(), kIndexReport, 7, "16.12.10"));
    }
  }
}

TEST(NexttimeIndexElaboration, AGoodActualForAFormalIndexIsAccepted) {
  for (const char* op : {"nexttime", "s_nexttime"}) {
    for (const char* actual : {"0", "1", "ONE", "int'(R)"}) {
      SCOPED_TRACE(std::string(op) + " " + actual);
      ExpectIndexAccepted(FormalIndexSource(op, actual));
    }
  }
}

}  // namespace
