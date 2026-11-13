#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "helpers_marked_reports.h"

using namespace delta;

namespace {

constexpr const char* kAutomaticReport =
    "an automatic variable may not stand in the clocking event or the "
    "expression2 of $";

void ExpectAutomaticReports(const MarkedSource& marked) {
  ExpectMarkedReports(marked, kAutomaticReport, "16.9.3");
}

TEST(SampledAutomatics, AnAutomaticSampledOrBesideAStaticClockIsAccepted) {
  ExpectAutomaticReports({"allowed forms",
                          "module m;\n"
                          "  logic clk, b, x, y, z, w;\n"
                          "  always @(posedge clk) begin\n"
                          "    automatic logic g = b;\n"
                          "    x <= $past(g);\n"
                          "    y <= $rose(g, @(posedge clk));\n"
                          "    z <= $past(b, 1, 1, @(posedge clk));\n"
                          "  end\n"
                          "  task automatic t1();\n"
                          "    static logic s = 0;\n"
                          "    @(posedge clk) w = $past(b, 1, s, @(posedge "
                          "clk)) | $rose(b, @(posedge s));\n"
                          "  endtask\n"
                          "  task static t2();\n"
                          "    logic q;\n"
                          "    @(posedge clk) w = $past(b, 1, q, @(posedge "
                          "clk)) & $fell(b, @(posedge q));\n"
                          "  endtask\n"
                          "endmodule\n",
                          {},
                          {"x <= $past(g)", "y <= $rose(g,", "z <= $past(b,",
                           "$past(b, 1, s,", "$past(b, 1, q,"}});
}

TEST(SampledAutomatics, AnAutomaticInAnyClockOrGateIsReported) {
  ExpectAutomaticReports(
      {"an automatic in an always block",
       "module m;\n"
       "  logic clk, b, x;\n"
       "  logic [3:0] v;\n"
       "  always @(posedge clk) begin\n"
       "    automatic logic g = b;\n"
       "    automatic int n = 0;\n"
       "    a1: assert property ($past(b, 1, 1, @(posedge g)) == b);\n"
       "    a2: assert property (@(posedge clk)"
       " $past(b, 1, 1, @(negedge g)) == b);\n"
       "    a3: assert property ($fell(b, @(posedge g)));\n"
       "    a4: assert property ($stable(b, @(posedge g)));\n"
       "    a5: assert property ($changed(b, @(posedge g)));\n"
       "    x <= $past(b, 1, g) ^ 1'b0;\n"
       "    x = $past(b, 1, g) ^ 1'b1;\n"
       "    x <= $past(b, 1, 1, @(posedge g)) | 1'b0;\n"
       "    x <= $rose(b, @(posedge g)) | 1'b1;\n"
       "    x <= $fell(b, @(posedge g)) & 1'b1;\n"
       "    x <= $stable(b, @(posedge g)) ^ 1'b0;\n"
       "    x <= $changed(b, @(posedge g)) ~^ 1'b0;\n"
       "    x <= $past(b, 1, v[n]);\n"
       "  end\n"
       "endmodule\n",
       {"a1:", "a2:", "a3:", "a4:", "a5:", "$past(b, 1, g) ^ 1'b0",
        "$past(b, 1, g) ^ 1'b1", "@(posedge g)) | 1'b0", "$rose(b,",
        "x <= $fell(b,", "x <= $stable(b,", "x <= $changed(b,", "v[n]"},
       {}});
}

TEST(SampledAutomatics, ASubroutineAutomaticIsReportedInEveryUnit) {
  const std::string kDecls = "  logic clk, b, w;\n";
  const std::string kFunctions =
      "  function automatic logic f1(logic g);\n"
      "    return $past(b, 1, 1, @(posedge g));\n"
      "  endfunction\n"
      "  function automatic logic f2();\n"
      "    logic h = b;\n"
      "    return $past(b, 1, h, @(posedge clk));\n"
      "  endfunction\n";
  const std::string kTasks =
      "  task automatic t1(input logic g);\n"
      "    @(posedge clk) w = $rose(b, @(posedge g));\n"
      "  endtask\n"
      "  task automatic t2();\n"
      "    logic h;\n"
      "    @(posedge clk) w = $past(b, 1, h, @(posedge clk));\n"
      "  endtask\n";
  const std::vector<std::string> kFunctionLines = {"return $past(b, 1, 1,",
                                                   "return $past(b, 1, h,"};
  const std::vector<std::string> kAllLines = {
      "return $past(b, 1, 1,", "return $past(b, 1, h,",
      "$rose(b, @(posedge g))", "w = $past(b, 1, h,"};
  ExpectAutomaticReports(
      {"module",
       "module m;\n" + kDecls + kFunctions + kTasks + "endmodule\n",
       kAllLines,
       {}});
  ExpectAutomaticReports(
      {"interface",
       "interface ifc;\n" + kDecls + kFunctions + kTasks +
           "endinterface\nmodule m;\n  ifc i();\nendmodule\n",
       kAllLines,
       {}});
  ExpectAutomaticReports({"program",
                          "program pg;\n" + kDecls + kFunctions + kTasks +
                              "endprogram\nmodule m;\n  pg p();\nendmodule\n",
                          kAllLines,
                          {}});
  ExpectAutomaticReports({"checker",
                          "checker ck;\n" + kDecls + kFunctions +
                              "endchecker\nmodule m;\n  ck k();\nendmodule\n",
                          kFunctionLines,
                          {}});
}

TEST(SampledAutomatics, AnAutomaticInAnInterfaceOrProgramIsReported) {
  ExpectAutomaticReports(
      {"interface and program procedures",
       "interface ifc(input logic clk, b);\n"
       "  logic x;\n"
       "  always @(posedge clk) begin\n"
       "    automatic logic g = b;\n"
       "    x <= $past(b, 1, g);\n"
       "  end\n"
       "endinterface\n"
       "program pg(input logic clk, b);\n"
       "  logic y;\n"
       "  initial begin\n"
       "    automatic logic e = b;\n"
       "    @(posedge clk) y = $past(b, 1, e, @(posedge clk));\n"
       "  end\n"
       "endprogram\n"
       "module m;\n"
       "  logic clk, b;\n"
       "  ifc i(clk, b);\n"
       "  pg p(clk, b);\n"
       "endmodule\n",
       {"$past(b, 1, g)", "$past(b, 1, e,"},
       {}});
}

TEST(SampledAutomatics, DISABLED_ALoopVariableInAClockOrGateIsReported) {
  ExpectAutomaticReports(
      {"for and foreach loop variables",
       "module m;\n"
       "  logic clk, b;\n"
       "  logic [3:0] q, v;\n"
       "  always @(posedge clk)\n"
       "    for (int i = 0; i < 4; i++) begin\n"
       "      q[i] <= $past(b, 1, i == 2);\n"
       "      q[0] <= $past(b, 1, i) ^ q[1];\n"
       "      q[i] <= $rose(b, @(posedge v[i]));\n"
       "      a1: assert property ($past(b, 1, i == 2) == q[i]);\n"
       "      a2: assert property ($rose(b, @(posedge v[i])));\n"
       "    end\n"
       "  always @(posedge clk)\n"
       "    foreach (v[k]) begin\n"
       "      q[k] <= $past(b, 1, k);\n"
       "      q[k] <= $past(b, 1, v[k]) ^ q[0];\n"
       "      q[k] <= $fell(b, @(posedge v[k]));\n"
       "    end\n"
       "  always @(posedge clk)\n"
       "    for (int j = 0; j < 4; j++) q[j] <= $past(v[j]);\n"
       "endmodule\n",
       {"$past(b, 1, i == 2);", "$past(b, 1, i) ^", "q[i] <= $rose(b,",
        "a1:", "a2:", "$past(b, 1, k);", "$past(b, 1, v[k])", "$fell(b,"},
       {"$past(v[j])"}});
}

TEST(SampledAutomatics, DISABLED_AnAutomaticInAGenerateBlockIsReported) {
  ExpectAutomaticReports(
      {"generate blocks",
       "module m;\n"
       "  logic clk, b, x;\n"
       "  for (genvar n = 0; n < 1; n++) begin : gl\n"
       "    always @(posedge clk) begin\n"
       "      automatic logic e = b;\n"
       "      x <= $past(b, 1, e) ^ 1'b0;\n"
       "      a1: assert property ($past(b, 1, e) == x);\n"
       "    end\n"
       "  end\n"
       "  if (1) begin : gc\n"
       "    always @(posedge clk) begin\n"
       "      automatic logic e = b;\n"
       "      x <= $past(b, 1, e) ^ 1'b1;\n"
       "      a2: assert property ($past(b, 1, e) != x);\n"
       "    end\n"
       "    function automatic logic gf(logic g);\n"
       "      return $past(b, 1, 1, @(posedge g));\n"
       "    endfunction\n"
       "  end\n"
       "endmodule\n",
       {"e) ^ 1'b0", "a1:", "e) ^ 1'b1", "a2:", "@(posedge g))"},
       {}});
}

TEST(SampledAutomatics, DISABLED_APackageUnitOrClassAutomaticIsReported) {
  ExpectAutomaticReports(
      {"packages, the compilation unit and classes",
       "package pk;\n"
       "  bit b;\n"
       "  function automatic logic pf(logic g);"
       " return $past(b, 1, 1, @(posedge g)); endfunction\n"
       "  function automatic logic pe(logic g, logic c);"
       " return $past(b, 1, g, @(posedge c)); endfunction\n"
       "endpackage\n"
       "bit ub;\n"
       "function automatic logic uf(logic g);"
       " return $past(ub, 1, 1, @(posedge g)); endfunction\n"
       "function automatic logic ue(logic g, logic c);"
       " return $past(ub, 1, g, @(posedge c)); endfunction\n"
       "class C;\n"
       "  bit clk, b, x;\n"
       "  task run();\n"
       "    logic g;\n"
       "    @(posedge clk) x = $past(b, 1, g, @(posedge clk));\n"
       "  endtask\n"
       "  function bit f();\n"
       "    automatic logic h;\n"
       "    return $rose(b, @(posedge h));\n"
       "  endfunction\n"
       "endclass\n"
       "module m;\n"
       "  logic clk, r;\n"
       "  C c = new;\n"
       "  always @(posedge clk) r <= pk::pf(clk) ^ pk::pe(r, clk) ^ uf(clk)"
       " ^ ue(r, clk);\n"
       "endmodule\n",
       {"function automatic logic pf(", "function automatic logic pe(",
        "function automatic logic uf(", "function automatic logic ue(",
        "x = $past(b, 1, g,", "$rose(b, @(posedge h))"},
       {}});
}

}  // namespace
