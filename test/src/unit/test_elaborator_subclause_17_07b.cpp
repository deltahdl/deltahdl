#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kNet = "a net cannot be declared inside checker";

void ExpectNets(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line : LinesHolding(src, "n_bad")) {
    EXPECT_TRUE(ReportedError(diags, kNet, line, "17.7")) << line;
  }
  for (uint32_t line : LinesHolding(src, "v_ok")) {
    EXPECT_FALSE(ErrorOnLine(diags, line)) << line;
  }
}

std::string InChecker(const std::string& preamble, const std::string& items) {
  std::string src = preamble;
  src += "checker chk(logic a);\n";
  src += items;
  src +=
      "endchecker\n"
      "module top;\n"
      "  logic a;\n"
      "  chk c(a);\n"
      "endmodule\n";
  return src;
}

TEST(CheckerNets, EachBuiltInNetKindInTheBodyIsReported) {
  ExpectNets(InChecker("",
                       "  tri n_bad1;\n"
                       "  wand n_bad2;\n"
                       "  wor n_bad3;\n"
                       "  triand n_bad4;\n"
                       "  trior n_bad5;\n"
                       "  tri0 n_bad6;\n"
                       "  tri1 n_bad7;\n"
                       "  supply0 n_bad8;\n"
                       "  supply1 n_bad9;\n"
                       "  trireg n_bad10;\n"
                       "  uwire n_bad11;\n"
                       "  interconnect n_bad12;\n"
                       "  logic v_ok1;\n"));
}

TEST(CheckerNets, EachFormOfANetDeclarationIsReported) {
  ExpectNets(InChecker("",
                       "  wire n_bad1 = a;\n"
                       "  wire logic [3:0] n_bad2;\n"
                       "  wire #1 n_bad3;\n"
                       "  trireg (small) n_bad4;\n"
                       "  wire n_bad5 [2];\n"
                       "  logic v_ok1 = a;\n"
                       "  logic [3:0] v_ok2;\n"
                       "  logic v_ok3 [2];\n"));
}

TEST(CheckerNets, DISABLED_ANetOfEachUserDefinedNettypeIsReported) {
  ExpectNets(
      InChecker("nettype logic mynet;\n"
                "nettype mynet alias_net;\n"
                "package P;\n"
                "  nettype logic pnet;\n"
                "endpackage\n"
                "import P::*;\n"
                "function automatic logic res(input logic d[]);\n"
                "  return d[0];\n"
                "endfunction\n"
                "nettype logic rnet with res;\n",
                "  mynet n_bad1;\n"
                "  P::pnet n_bad2;\n"
                "  pnet n_bad3;\n"
                "  $unit::mynet n_bad4;\n"
                "  alias_net n_bad5;\n"
                "  rnet n_bad6;\n"
                "  logic v_ok1;\n"));
}

TEST(CheckerNets, DISABLED_AUserDefinedNetInEachNestedPlaceIsReported) {
  ExpectNets(InChecker("nettype logic mynet;\n",
                       "  if (1) begin : g\n"
                       "    mynet n_bad1;\n"
                       "    logic v_ok1;\n"
                       "  end\n"
                       "  for (genvar i = 0; i < 1; i++) begin : h\n"
                       "    mynet n_bad2;\n"
                       "  end\n"
                       "  case (1)\n"
                       "    1: begin : k\n"
                       "      mynet n_bad3;\n"
                       "    end\n"
                       "  endcase\n"
                       "  checker inner;\n"
                       "    mynet n_bad4;\n"
                       "    wire n_bad5;\n"
                       "    logic v_ok2;\n"
                       "  endchecker\n"
                       "  inner ii();\n"));
}

TEST(CheckerNets, DISABLED_AnImplicitNetInACheckerIsReported) {
  ExpectNets(InChecker("",
                       "  checker inner(logic p);\n"
                       "  endchecker\n"
                       "  assign n_bad1 = a;\n"
                       "  inner i1(n_bad2);\n"
                       "  logic v_ok1;\n"
                       "  assign v_ok1 = a;\n"
                       "  logic v_ok2;\n"
                       "  inner i2(v_ok2);\n"));
}

TEST(CheckerNets, EachVariableFormIsAccepted) {
  ExpectNets(
      InChecker("typedef enum {E0, E1} e_t;\n"
                "typedef struct packed { bit [3:0] h, l; } pair_t;\n",
                "  int v_ok1;\n"
                "  logic [7:0] v_ok2;\n"
                "  e_t v_ok3;\n"
                "  pair_t v_ok4;\n"
                "  bit v_ok5 [4];\n"
                "  var logic v_ok6;\n"));
}

TEST(CheckerNets, AVariableInEachGenerateBlockIsAccepted) {
  ExpectNets(InChecker("",
                       "  if (1) begin : g\n"
                       "    bit v_ok1;\n"
                       "    bit v_ok2 = 1'b1;\n"
                       "  end\n"
                       "  for (genvar i = 0; i < 2; i++) begin : h\n"
                       "    bit v_ok3;\n"
                       "    bit v_ok4 = 1'b1;\n"
                       "  end\n"
                       "  case (1)\n"
                       "    1: begin : k\n"
                       "      bit v_ok5;\n"
                       "      bit v_ok6 = 1'b0;\n"
                       "    end\n"
                       "  endcase\n"));
}

}  // namespace
