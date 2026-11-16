#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(RealCoverpointTransitionBin, TransitionBinOfRealCoverpointIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  bit [1:0] x;\n"
      "  covergroup cg;\n"
      "    a: coverpoint r { bins one = {[1.0:2.0]}; bins t = (1.0 => 2.0); }\n"
      "    b: coverpoint r { bins one = {[1.0:2.0]};\n"
      "                      ignore_bins u = (2.0 => 3.0); }\n"
      "    c: coverpoint x { bins t = (1 => 2); }\n"
      "  endgroup\n"
      "  cg cv = new;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5u, 7u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a coverpoint of a real expression takes no "
                              "transition bin",
                              line, "19.5.2"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(TransitionLength, DISABLED_ARepeatCountEvaluatingToOneIsError) {
  const std::string kBins =
      "  bit [1:0] v;\n"
      "  covergroup cg;\n"
      "    coverpoint v {\n"
      "      bins b = (0 [* P]);\n"
      "      bins c = (0 [* 2-1]);\n"
      "      bins d = (0 [* 1:P]);\n"
      "      bins f = (0 [* P+1]);\n"
      "    }\n"
      "  endgroup\n";
  for (const std::string& src :
       {"module m;\n  parameter int P = 1;\n" + kBins + "endmodule\n",
        "class k;\n  localparam int P = 1;\n" + kBins +
            "  function new; cg = new; endfunction\nendclass\n"}) {
    ElabFixture f;
    ElaborateSrc(src, f);
    for (uint32_t line : {6u, 7u, 8u}) {
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                                "a transition of length 0 is illegal; its "
                                "trans_set covers a single value range",
                                line, "19.5.2"))
          << line;
    }
    EXPECT_EQ(f.diag.ErrorCount(), 3u);
  }
}

}  // namespace
