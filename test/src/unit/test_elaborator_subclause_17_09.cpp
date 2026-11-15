#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

void ExpectAccepted(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

const char* const kModuleHead =
    "module top;\n"
    "  logic clk = 0, a = 0, b = 0;\n"
    "  sequence s;\n"
    "    @(posedge clk) a;\n"
    "  endsequence\n";

TEST(TriggeredInCombinationalContext, EachModuleFormIsAccepted) {
  std::string src = kModuleHead;
  src +=
      "  sequence sa(x);\n"
      "    @(posedge clk) x;\n"
      "  endsequence\n"
      "  function automatic bit read_s();\n"
      "    return s.triggered;\n"
      "  endfunction\n"
      "  let f = s.triggered;\n"
      "  logic x1, y1, e1, e2, y2, x3, y3, x4, y4;\n"
      "  assign x1 = s.triggered;\n"
      "  wire n = s.triggered;\n"
      "  always_comb y1 = s.triggered;\n"
      "  assign e1 = s.triggered && b;\n"
      "  always_comb e2 = b ? s.triggered : 1'b0;\n"
      "  always_comb y2 = read_s();\n"
      "  assign x3 = f;\n"
      "  always_comb y3 = f;\n"
      "  assign x4 = sa(b).triggered;\n"
      "  always_comb y4 = sa(b).triggered;\n"
      "endmodule\n";
  ExpectAccepted(src);
}

TEST(TriggeredInCombinationalContext, ASequenceNamedFromElsewhereIsAccepted) {
  ExpectAccepted(
      "package pk;\n"
      "  sequence ps(c, x);\n"
      "    @(posedge c) x;\n"
      "  endsequence\n"
      "endpackage\n"
      "sequence us;\n"
      "  @(posedge top.clk) top.b;\n"
      "endsequence\n"
      "module sub(input logic clk, a);\n"
      "  sequence hs;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0, a = 0, b = 0;\n"
      "  sub u(clk, a);\n"
      "  logic x1, y1, x2, y2, x3, y3;\n"
      "  assign x1 = u.hs.triggered;\n"
      "  always_comb y1 = u.hs.triggered;\n"
      "  assign x2 = pk::ps(clk, a).triggered;\n"
      "  always_comb y2 = pk::ps(clk, a).triggered;\n"
      "  assign x3 = us.triggered;\n"
      "  always_comb y3 = us.triggered;\n"
      "endmodule\n");
}

TEST(TriggeredInCombinationalContext, EachEnclosingScopeIsAccepted) {
  std::string src = kModuleHead;
  src +=
      "  if (1) begin : g\n"
      "    logic gx, gy;\n"
      "    assign gx = s.triggered;\n"
      "    always_comb gy = s.triggered;\n"
      "  end\n"
      "  ifc i(clk, a);\n"
      "  prg p(clk, a);\n"
      "endmodule\n"
      "interface ifc(input logic clk, a);\n"
      "  sequence is;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  logic ix, iy;\n"
      "  assign ix = is.triggered;\n"
      "  always_comb iy = is.triggered;\n"
      "endinterface\n"
      "program prg(input logic clk, a);\n"
      "  sequence ps;\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "  logic px;\n"
      "  assign px = ps.triggered;\n"
      "endprogram\n";
  ExpectAccepted(src);
}

TEST(TriggeredInCombinationalContext, EachCheckerFormIsAccepted) {
  std::string src =
      "checker ck(sequence st, event clock = $inferred_clock);\n"
      "  sequence cs;\n"
      "    @clock 1'b1;\n"
      "  endsequence\n"
      "  let lf = st.triggered;\n"
      "  bit v1, v2, w1, w2, v3, w3;\n"
      "  assign v1 = st.triggered;\n"
      "  assign v2 = cs.triggered;\n"
      "  always_comb w1 = st.triggered;\n"
      "  always_comb w2 = cs.triggered;\n"
      "  assign v3 = lf;\n"
      "  always_comb w3 = lf;\n"
      "endchecker\n";
  src += kModuleHead;
  src +=
      "  default clocking @(posedge clk); endclocking\n"
      "  ck c(s);\n"
      "endmodule\n";
  ExpectAccepted(src);
}

}  // namespace
