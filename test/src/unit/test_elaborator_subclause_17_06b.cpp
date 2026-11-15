#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kReport =
    "cannot be instantiated in a procedure of a checker";

const char* const kCg =
    "  covergroup cg @(posedge clk);\n"
    "    cp: coverpoint a;\n"
    "  endgroup\n";

const char* const kTop =
    "module top;\n"
    "  logic clk, a;\n"
    "  chk c(clk, a);\n"
    "endmodule\n";

size_t ReportsOnLine(const std::vector<Diagnostic>& diags, uint32_t line) {
  size_t n = 0;
  for (const auto& diag : diags) {
    if (diag.loc.line == line &&
        diag.message.find(kReport) != std::string::npos) {
      ++n;
    }
  }
  return n;
}

void ExpectPlacement(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  const auto& diags = f.diag.Diagnostics();
  const auto kReported = LinesHolding(src, "cg_p");
  EXPECT_FALSE(kReported.empty());
  for (uint32_t line : kReported) {
    EXPECT_TRUE(ReportedError(diags, kReport, line, "17.6")) << line;
  }
  for (uint32_t line : LinesHolding(src, "cg_b")) {
    EXPECT_FALSE(ErrorOnLine(diags, line)) << line;
  }
}

std::string InChecker(const std::string& items) {
  std::string src = "checker chk(logic clk, logic a);\n";
  src += items;
  src += "endchecker\n";
  src += kTop;
  return src;
}

TEST(CheckerCovergroupPlacement, AnInstanceInEachProcedureIsReported) {
  for (const char* proc : {"initial", "always_comb", "always_latch",
                           "always_ff @(posedge clk)", "final"}) {
    std::string items = kCg;
    items += "  cg cg_b = new();\n  ";
    items += proc;
    items += " begin\n    automatic cg cg_p = new();\n  end\n";
    SCOPED_TRACE(proc);
    ExpectPlacement(InChecker(items));
  }
}

TEST(CheckerCovergroupPlacement, AStaticInstanceWithNoInitializerIsReported) {
  ExpectPlacement(InChecker(std::string(kCg) + "  cg cg_b;\n"
                                               "  initial begin\n"
                                               "    cg cg_p;\n"
                                               "  end\n"));
}

TEST(CheckerCovergroupPlacement, AnInstanceInANestedBlockOrBranchIsReported) {
  ExpectPlacement(InChecker(std::string(kCg) +
                            "  always_ff @(posedge clk) begin\n"
                            "    begin : inner\n"
                            "      automatic cg cg_p1 = new();\n"
                            "    end\n"
                            "    if (a) begin\n"
                            "      automatic cg cg_p2 = new();\n"
                            "    end\n"
                            "  end\n"));
}

TEST(CheckerCovergroupPlacement, EachInstanceOfOneDeclarationIsReported) {
  const std::string kSrc = InChecker(std::string(kCg) +
                                     "  initial begin\n"
                                     "    cg cg_1, cg_2;\n"
                                     "  end\n");
  ElabFixture f;
  ElaborateSrc(kSrc, f, "top");
  EXPECT_EQ(ReportsOnLine(f.diag.Diagnostics(), LineHolding(kSrc, "cg_1")), 2u);
}

struct TypeSource {
  const char* name;
  const char* preamble;
  const char* items;
  const char* type;
};

const char* const kPackage =
    "package p;\n"
    "  covergroup cg with function sample(bit x);\n"
    "    cp: coverpoint x;\n"
    "  endgroup\n"
    "endpackage\n";

TEST(CheckerCovergroupPlacement, DISABLED_ATypeDeclaredElsewhereIsReported) {
  const std::string kOwnTypedef = std::string(kCg) + "  typedef cg cg_t;\n";
  const TypeSource kSources[] = {
      {"package", kPackage, "", "p::cg"},
      {"import", kPackage, "  import p::*;\n", "cg"},
      {"compilation unit",
       "covergroup cg_u with function sample(bit x);\n"
       "  cp: coverpoint x;\n"
       "endgroup\n",
       "", "cg_u"},
      {"own typedef", "", kOwnTypedef.c_str(), "cg_t"},
      {"package typedef", kPackage, "  typedef p::cg cg_t;\n", "cg_t"},
  };
  for (const auto& source : kSources) {
    std::string items = source.items;
    items += "  ";
    items += source.type;
    items += " cg_b = new();\n  always_ff @(posedge clk) begin\n    automatic ";
    items += source.type;
    items += " cg_p = new();\n  end\n";
    SCOPED_TRACE(source.name);
    ExpectPlacement(source.preamble + InChecker(items));
  }
}

TEST(CheckerCovergroupPlacement,
     DISABLED_AnEnclosingModulesCovergroupIsReported) {
  ExpectPlacement(
      "module top;\n"
      "  covergroup cg_m with function sample(bit x);\n"
      "    cp: coverpoint x;\n"
      "  endgroup\n"
      "  checker chk(logic clk, logic a);\n"
      "    cg_m cg_b = new();\n"
      "    initial begin\n"
      "      automatic cg_m cg_p = new();\n"
      "    end\n"
      "  endchecker\n"
      "  logic clk, a;\n"
      "  chk c(clk, a);\n"
      "endmodule\n");
}

TEST(CheckerCovergroupPlacement,
     DISABLED_AProcedureInEachGenerateBlockIsChecked) {
  ExpectPlacement(InChecker(std::string(kCg) +
                            "  if (1) begin : g\n"
                            "    always_ff @(posedge clk) begin\n"
                            "      automatic cg cg_p1 = new();\n"
                            "    end\n"
                            "  end\n"
                            "  for (genvar i = 0; i < 1; i++) begin : h\n"
                            "    initial begin\n"
                            "      automatic cg cg_p2 = new();\n"
                            "    end\n"
                            "  end\n"
                            "  case (1)\n"
                            "    1: begin : k\n"
                            "      final begin\n"
                            "        automatic cg cg_p3 = new();\n"
                            "      end\n"
                            "    end\n"
                            "  endcase\n"));
}

TEST(CheckerCovergroupPlacement,
     DISABLED_AGenerateBlocksOwnCovergroupIsChecked) {
  ExpectPlacement(
      InChecker("  if (1) begin : g\n"
                "    covergroup cg3 @(posedge clk);\n"
                "      cp: coverpoint a;\n"
                "    endgroup\n"
                "    cg3 cg_b = new();\n"
                "    always_ff @(posedge clk) begin\n"
                "      automatic cg3 cg_p = new();\n"
                "    end\n"
                "  end\n"));
}

TEST(CheckerCovergroupPlacement, DISABLED_ANestedCheckersProcedureIsChecked) {
  ExpectPlacement(InChecker(std::string(kCg) +
                            "  checker inner;\n"
                            "    cg cg_b = new();\n"
                            "    always_ff @(posedge clk) begin\n"
                            "      automatic cg cg_p = new();\n"
                            "    end\n"
                            "  endchecker\n"
                            "  inner n();\n"));
}

}  // namespace
