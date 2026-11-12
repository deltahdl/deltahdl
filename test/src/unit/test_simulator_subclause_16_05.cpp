#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ObservedRegionEvaluationSim,
     InactiveAndNbaWritesAtTheTickAreSeenThroughFunctionBodies) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  logic clk = 0;\n"
                       "  int vi = 0, vn = 0;\n"
                       "  event e;\n"
                       "  function int pi(); return vi; endfunction\n"
                       "  function int pn(); return vn; endfunction\n"
                       "  always @(posedge clk) begin #0 vi = 1; end\n"
                       "  always @(posedge clk) vn <= 1;\n"
                       "  always @(posedge clk) ->> e;\n"
                       "  ai: assert property (@(posedge clk) pi() == 1) "
                       "$display(\"ai pass\"); else $display(\"ai fail\");\n"
                       "  an: assert property (@(posedge clk) pn() == 1) "
                       "$display(\"an pass\"); else $display(\"an fail\");\n"
                       "  ae: assert property (@(posedge clk) e.triggered) "
                       "$display(\"ae pass\"); else $display(\"ae fail\");\n"
                       "  always @(posedge clk) begin\n"
                       "    pi1: assert property (pi() == 1) $display(\"pi1 "
                       "pass\"); else $display(\"pi1 fail\");\n"
                       "    pn1: assert property (pn() == 1) $display(\"pn1 "
                       "pass\"); else $display(\"pn1 fail\");\n"
                       "  end\n"
                       "  initial #5 clk = 1;\n"
                       "endmodule\n",
                       f),
            "ai pass\nan pass\nae pass\npi1 pass\npn1 pass\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ObservedRegionEvaluationSim,
     InactiveAndNbaWritesAtTheTickAreSeenThroughConstCasts) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  logic clk = 0;\n"
                       "  int vi = 0, vn = 0;\n"
                       "  always @(posedge clk) begin #0 vi = 1; end\n"
                       "  always @(posedge clk) vn <= 1;\n"
                       "  ci: assert property (@(posedge clk) const'(vi) == 1) "
                       "$display(\"ci pass\"); else $display(\"ci fail\");\n"
                       "  cn: assert property (@(posedge clk) const'(vn) == 1) "
                       "$display(\"cn pass\"); else $display(\"cn fail\");\n"
                       "  initial #5 clk = 1;\n"
                       "endmodule\n",
                       f),
            "ci pass\ncn pass\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ObservedRegionEvaluationSim, ReactiveRegionSetWritesAtTheTickAreNotSeen) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureAllTops(
          "module m;\n"
          "  logic clk = 0;\n"
          "  int vn = 0, vr = 0, vc = 0, vri = 0, vrn = 0;\n"
          "  event er;\n"
          "  function int pn(); return vn; endfunction\n"
          "  function int pr(); return vr; endfunction\n"
          "  function int pri(); return vri; endfunction\n"
          "  function int prn(); return vrn; endfunction\n"
          "  always @(posedge clk) vn <= 1;\n"
          "  an: assert property (@(posedge clk) pn() == 1) $display(\"an "
          "pass\"); else $display(\"an fail\");\n"
          "  ar: assert property (@(posedge clk) pr() == 0) $display(\"ar "
          "pass\"); else $display(\"ar fail\");\n"
          "  ac: assert property (@(posedge clk) const'(vc) == 0) "
          "$display(\"ac pass\"); else $display(\"ac fail\");\n"
          "  ae: assert property (@(posedge clk) !er.triggered) $display(\"ae "
          "pass\"); else $display(\"ae fail\");\n"
          "  ari: assert property (@(posedge clk) pri() == 0) $display(\"ari "
          "pass\"); else $display(\"ari fail\");\n"
          "  arn: assert property (@(posedge clk) prn() == 0) $display(\"arn "
          "pass\"); else $display(\"arn fail\");\n"
          "  initial begin\n"
          "    #5 clk = 1;\n"
          "    #5 $display(\"%0d %0d %0d %0d\", vr, vc, vri, vrn);\n"
          "  end\n"
          "endmodule\n"
          "program p;\n"
          "  initial begin\n"
          "    @(posedge m.clk);\n"
          "    m.vr = 1;\n"
          "    m.vc = 1;\n"
          "    -> m.er;\n"
          "    m.vrn <= 1;\n"
          "    #0 m.vri = 1;\n"
          "    #20;\n"
          "  end\n"
          "endprogram\n",
          f),
      "an pass\nar pass\nac pass\nae pass\nari pass\narn pass\n1 1 1 1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ObservedRegionEvaluationSim,
     AProgramWriteThatWakesAModuleProcessGivesOneVerdict) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops("module m;\n"
                              "  logic clk = 0;\n"
                              "  int w = 0, x = 0, verdicts = 0;\n"
                              "  function int px(); return x; endfunction\n"
                              "  always @(w) x = w;\n"
                              "  a1: assert property (@(posedge clk) px() == "
                              "0) verdicts++; else verdicts += 100;\n"
                              "  initial begin\n"
                              "    #5 clk = 1;\n"
                              "    #5 $display(\"%0d %0d\", x, verdicts);\n"
                              "  end\n"
                              "endmodule\n"
                              "program p;\n"
                              "  initial begin\n"
                              "    @(posedge m.clk);\n"
                              "    m.w = 1;\n"
                              "    #20;\n"
                              "  end\n"
                              "endprogram\n",
                              f),
            "1 1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(
    ObservedRegionEvaluationSim,
    DISABLED_AFunctionBodyReadsTheCurrentValueOfAVariableAnotherAssertionSamples) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  logic clk = 0;\n"
                 "  int va = 0, vi = 0, vn = 0;\n"
                 "  function int pa(); return va; endfunction\n"
                 "  function int pi(); return vi; endfunction\n"
                 "  function int pn(); return vn; endfunction\n"
                 "  always @(posedge clk) va = 1;\n"
                 "  always @(posedge clk) begin #0 vi = 1; end\n"
                 "  always @(posedge clk) vn <= 1;\n"
                 "  sa: assert property (@(posedge clk) va == 0 && vi == 0 && "
                 "vn == 0) $display(\"sa pass\"); else $display(\"sa fail\");\n"
                 "  fa: assert property (@(posedge clk) pa() == 1) "
                 "$display(\"fa pass\"); else $display(\"fa fail\");\n"
                 "  fi: assert property (@(posedge clk) pi() == 1) "
                 "$display(\"fi pass\"); else $display(\"fi fail\");\n"
                 "  fn: assert property (@(posedge clk) pn() == 1) "
                 "$display(\"fn pass\"); else $display(\"fn fail\");\n"
                 "  initial #5 clk = 1;\n"
                 "endmodule\n",
                 f),
      "sa pass\nfa pass\nfi pass\nfn pass\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ObservedRegionEvaluationSim,
     EachPlaceAndKindSeesTheNbaWriteAndNotTheProgramWrite) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "interface ifc(input logic clk);\n"
                "  function int qn(); return m.vn; endfunction\n"
                "  function int qr(); return m.vr; endfunction\n"
                "  ia: assert property (@(posedge clk) qn() == 1 && qr() == 0) "
                "$display(\"ifc pass\"); else $display(\"ifc FAIL\");\n"
                "endinterface\n"
                "checker chk(logic clk);\n"
                "  function int qn(); return m.vn; endfunction\n"
                "  function int qr(); return m.vr; endfunction\n"
                "  ca: assert property (@(posedge clk) qn() == 1 && qr() == 0) "
                "$display(\"chk pass\"); else $display(\"chk FAIL\");\n"
                "endchecker\n"
                "module m;\n"
                "  logic clk = 0;\n"
                "  int vn = 0, vr = 0;\n"
                "  function int pn(); return vn; endfunction\n"
                "  function int pr(); return vr; endfunction\n"
                "  always @(posedge clk) vn <= 1;\n"
                "  ifc i(clk);\n"
                "  chk c(clk);\n"
                "  p pr0(clk);\n"
                "  if (1) begin : g\n"
                "    ga: assert property (@(posedge clk) pn() == 1 && pr() == "
                "0) $display(\"gen pass\"); else $display(\"gen FAIL\");\n"
                "  end\n"
                "  am: assume property (@(posedge clk) pn() == 1 && pr() == 0) "
                "$display(\"assume pass\"); else $display(\"assume FAIL\");\n"
                "  cp: cover property (@(posedge clk) pn() == 1 && pr() == 0) "
                "$display(\"cover property hit\");\n"
                "  cs: cover sequence (@(posedge clk) pn() == 1 && pr() == 0) "
                "$display(\"cover sequence hit\");\n"
                "  initial #5 clk = 1;\n"
                "endmodule\n"
                "program p(input logic clk);\n"
                "  function int qn(); return m.vn; endfunction\n"
                "  function int qr(); return m.vr; endfunction\n"
                "  pa: assert property (@(posedge clk) qn() == 1 && qr() == 0) "
                "$display(\"prog pass\"); else $display(\"prog FAIL\");\n"
                "  initial begin\n"
                "    @(posedge clk);\n"
                "    m.vr = 1;\n"
                "    #20;\n"
                "  end\n"
                "endprogram\n",
                f),
            "assume pass\ncover property hit\ncover sequence hit\ngen "
            "pass\nifc pass\nchk pass\nprog pass\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
