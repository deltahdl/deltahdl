#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_final_output.h"

using namespace delta;

namespace {

using Lines = std::vector<std::string>;

std::string Shown(const std::string& label, const Lines& names) {
  std::string text = "  final $display(\"";
  text += label;
  for (size_t i = 0; i < names.size(); ++i) text += " %0d";
  text += "\"";
  for (const auto& name : names) {
    text += ", $rtoi(";
    text += name;
    text += ".get_inst_coverage())";
  }
  text += ");\n";
  return text;
}

std::string Group(const std::string& type, const std::string& points) {
  std::string text = "  covergroup ";
  text += type;
  text += " @(posedge clk);\n";
  text += points;
  text += "  endgroup\n";
  return text;
}

const char* const kOne = "    cp: coverpoint a { bins one = {1'b1}; }\n";

std::string Clocked(const std::string& cu, const std::string& header,
                    const std::string& body, const std::string& top) {
  std::string src = cu;
  src += "checker chk(";
  src += header;
  src += ");\n";
  src += body;
  src +=
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n";
  src += top;
  src += "  initial #52 $finish;\nendmodule\n";
  return src;
}

TEST(CheckerCovergroupPlaces, EachInstanceOfOneDeclarationIsSampled) {
  EXPECT_EQ(
      SortedOutput(Clocked("", "logic clk, a",
                           Group("cg", kOne) + "  cg x = new(), y = new();\n" +
                               Shown("both", {"x", "y"}),
                           "  logic a = 1;\n  chk c(clk, a);\n")),
      (Lines{"both 100 100"}));
}

TEST(CheckerCovergroupPlaces, EachGenerateBlockOfTheCheckerIsSampled) {
  std::string body = "  if (1) begin : g\n";
  body += Group("gcg", kOne);
  body += "    gcg i = new();\n  end\n";
  body += "  for (genvar k = 0; k < 2; k++) begin : h\n";
  body += Group("hcg", "    cp: coverpoint a { bins one = {1'b1}; }\n");
  body += "    hcg i = new();\n  end\n  case (1)\n    1: begin : k\n";
  body += Group("kcg", kOne);
  body += "      kcg i = new();\n    end\n  endcase\n  generate\n";
  body += Group("rcg", kOne);
  body += "    rcg ri = new();\n  endgenerate\n";
  body += Shown("gen", {"g.i", "h[0].i", "h[1].i", "k.i", "ri"});
  EXPECT_EQ(SortedOutput(Clocked("", "logic clk, a", body,
                                 "  logic a = 1;\n  chk c(clk, a);\n")),
            (Lines{"gen 100 100 100 100 100"}));
}

std::string Nested(const std::string& name, const std::string& label) {
  std::string text = "checker ";
  text += name;
  text += "(logic clk, a);\n";
  text += Group("cg", kOne);
  text += "  cg i = new();\n";
  text += Shown(label, {"i"});
  text += "endchecker\n";
  return text;
}

TEST(CheckerCovergroupPlaces, EachPlaceACheckerIsDeclaredIsSampled) {
  std::string src = "package p;\n";
  src += Nested("pchk", "package");
  src += "endpackage\nchecker outer(logic clk, a);\n";
  src += Nested("inner", "nested");
  src += "  inner n(clk, a);\nendchecker\ninterface ifc(input logic clk, a);\n";
  src += Nested("ichk", "interface");
  src += "  ichk u(clk, a);\nendinterface\nprogram prg(input logic clk, a);\n";
  src += Nested("gchk", "program");
  src +=
      "  gchk u(clk, a);\n"
      "  initial #60;\n"
      "endprogram\n"
      "module top;\n"
      "  logic clk = 0, a = 1;\n"
      "  always #5 clk = ~clk;\n";
  src += Nested("mchk", "module");
  src += Nested("achk", "procedural");
  src +=
      "  mchk u(clk, a);\n"
      "  always @(posedge clk) achk v(clk, a);\n"
      "  p::pchk pu(clk, a);\n"
      "  outer o(clk, a);\n"
      "  ifc i(clk, a);\n"
      "  prg g(clk, a);\n"
      "  initial #52 $finish;\n"
      "endmodule\n";
  EXPECT_EQ(SortedOutput(src),
            (Lines{"interface 100", "module 100", "nested 100", "package 100",
                   "procedural 100", "program 100"}));
}

TEST(CheckerCovergroupPlaces,
     DISABLED_ACheckerDeclaredInAGenerateBlockIsSampled) {
  std::string src = "checker outer(logic clk, a);\n  if (1) begin : g\n";
  src += Nested("cchk", "checker");
  src +=
      "    cchk u(clk, a);\n"
      "  end\n"
      "endchecker\n"
      "interface ifc(input logic clk, a);\n"
      "  if (1) begin : g\n";
  src += Nested("ichk", "interface");
  src +=
      "    ichk u(clk, a);\n"
      "  end\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk = 0, a = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  if (1) begin : g\n";
  src += Nested("mchk", "module");
  src +=
      "    mchk u(clk, a);\n"
      "  end\n"
      "  outer o(clk, a);\n"
      "  ifc i(clk, a);\n"
      "  initial #52 $finish;\n"
      "endmodule\n";
  EXPECT_EQ(SortedOutput(src),
            (Lines{"checker 100", "interface 100", "module 100"}));
}

TEST(CheckerCovergroupReferences, DISABLED_AMultiBitFormalIsBinnedAtFullWidth) {
  SimFixture f;
  EXPECT_EQ(
      SortedOutput(Clocked("", "logic clk, int n, logic [3:0] w, logic t",
                           Group("cg",
                                 "    np: coverpoint n { bins b = {1234}; }\n"
                                 "    wp: coverpoint w { bins b = {4'd9}; }\n"
                                 "    tp: coverpoint t { bins lo = {1'b0}; "
                                 "bins hi = {1'b1}; }\n"
                                 "    x: cross wp, tp;\n") +
                               "  cg i = new();\n" +
                               Shown("wide", {"i.np", "i.wp", "i.x"}),
                           "  int n = 1234;\n"
                           "  logic [3:0] w = 4'd9;\n"
                           "  logic t = 0;\n"
                           "  always @(negedge clk) t = !t;\n"
                           "  chk c(clk, n, w, t);\n"),
                   f),
      (Lines{"wide 100 100 100"}));
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(CheckerCovergroupReferences,
     DISABLED_AnUntypedFormalOrAnExpressionIsBinned) {
  EXPECT_EQ(SortedOutput(Clocked(
                "", "logic clk, untyped u, logic [3:0] w",
                Group("cg",
                      "    up: coverpoint u { bins b = {6}; }\n"
                      "    ep: coverpoint w + 4'd0 { bins b = {4'd9}; }\n") +
                    "  cg i = new();\n" + Shown("forms", {"i.up", "i.ep"}),
                "  logic [3:0] w = 4'd9;\n  chk c(clk, 6, w);\n")),
            (Lines{"forms 100 100"}));
}

TEST(CheckerCovergroupReferences, ACheckerVariablesChangingValuesAreBinned) {
  EXPECT_EQ(SortedOutput(Clocked(
                "", "logic clk",
                "  bit t = 0;\n"
                "  bit [3:0] cv = 0;\n"
                "  always_ff @(posedge clk) begin\n"
                "    t <= !t;\n"
                "    cv <= cv + 4'd1;\n"
                "  end\n" +
                    Group("cg",
                          "    tp: coverpoint t { bins lo = {1'b0}; "
                          "bins hi = {1'b1}; }\n"
                          "    cp: coverpoint cv { bins b[] = {[0:4]}; }\n"
                          "    np: coverpoint cv { bins b = {[5:15]}; }\n") +
                    "  cg i = new();\n" + Shown("cv", {"i.tp", "i.cp", "i.np"}),
                "  chk c(clk);\n")),
            (Lines{"cv 100 100 0"}));
}

std::string Reader(const std::string& name, const std::string& label,
                   const std::string& var) {
  std::string text = "checker ";
  text += name;
  text += "(logic clk);\n";
  text += Group("cg", "    vp: coverpoint " + var + " { bins b = {4'd7}; }\n");
  text += "  cg i = new();\n";
  text += Shown(label, {"i"});
  text += "endchecker\n";
  return text;
}

TEST(CheckerCovergroupReferences, AnEnclosingScopesVariableIsBinned) {
  std::string src = "checker outer(logic clk);\n  bit [3:0] ov = 4'd7;\n";
  src += Reader("inner", "checker", "ov");
  src += "  inner n(clk);\nendchecker\ninterface ifc(input logic clk);\n";
  src += "  bit [3:0] iv = 4'd7;\n";
  src += Reader("ichk", "interface", "iv");
  src += "  ichk u(clk);\nendinterface\nprogram prg(input logic clk);\n";
  src += "  bit [3:0] pv = 4'd7;\n";
  src += Reader("gchk", "program", "pv");
  src +=
      "  gchk u(clk);\n"
      "  initial #60;\n"
      "endprogram\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  bit [3:0] mv = 4'd7;\n";
  src += Reader("mchk", "module", "mv");
  src +=
      "  mchk u(clk);\n"
      "  outer o(clk);\n"
      "  ifc i(clk);\n"
      "  prg g(clk);\n"
      "  initial #52 $finish;\n"
      "endmodule\n";
  EXPECT_EQ(SortedOutput(src), (Lines{"checker 100", "interface 100",
                                      "module 100", "program 100"}));
}

TEST(CheckerCovergroupReferences,
     DISABLED_AGenerateBlockVariableEnclosingTheCheckerIsBinned) {
  std::string src =
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  if (1) begin : g\n"
      "    bit [3:0] gv = 4'd7;\n";
  src += Reader("gchk", "generate", "gv");
  src +=
      "    gchk u(clk);\n"
      "  end\n"
      "  initial #52 $finish;\n"
      "endmodule\n";
  EXPECT_EQ(SortedOutput(src), (Lines{"generate 100"}));
}

TEST(CheckerCovergroupReferences, APackageOrCompilationUnitVariableIsBinned) {
  EXPECT_EQ(SortedOutput(
                Clocked("package p;\n"
                        "  bit [3:0] pv = 4'd5;\n"
                        "endpackage\n"
                        "bit [3:0] uv = 4'd6;\n"
                        "import p::*;\n",
                        "logic clk",
                        Group("cg",
                              "    qp: coverpoint p::pv { bins b = {4'd5}; }\n"
                              "    ip: coverpoint pv { bins b = {4'd5}; }\n"
                              "    up: coverpoint uv { bins b = {4'd6}; }\n"
                              "    sp: coverpoint $unit::uv "
                              "{ bins b = {4'd6}; }\n") +
                            "  cg i = new();\n" +
                            Shown("outside", {"i.qp", "i.ip", "i.up", "i.sp"}),
                        "  chk c(clk);\n")),
            (Lines{"outside 100 100 100 100"}));
}

TEST(CheckerCovergroupReferences,
     DISABLED_AGenerateBlockVariableBesideAFormalIsBinned) {
  std::string body = "  if (1) begin : g\n    bit [3:0] gv = 4'd8;\n";
  body += Group("gcg",
                "    gp: coverpoint gv { bins b = {4'd8}; }\n"
                "    fp: coverpoint a { bins b = {1'b1}; }\n");
  body += "    gcg i = new();\n  end\n";
  body += Shown("gen", {"g.i.gp", "g.i.fp"});
  EXPECT_EQ(SortedOutput(Clocked("", "logic clk, a", body,
                                 "  logic a = 1;\n  chk c(clk, a);\n")),
            (Lines{"gen 100 100"}));
}

std::string Optioned(const std::string& type, const std::string& at_least) {
  std::string text = "  covergroup ";
  text += type;
  text += " @(posedge clk);\n    option.at_least = ";
  text += at_least;
  text += ";\n    cp: coverpoint 1'b1 { bins one = {1'b1}; }\n  endgroup\n";
  return text;
}

std::string Counted(const std::string& type, const std::string& event,
                    int at_least) {
  std::string text = "  covergroup ";
  text += type;
  text += " @(posedge ";
  text += event;
  text += ");\n    option.at_least = ";
  text += std::to_string(at_least);
  text += ";\n    cp: coverpoint 1'b1 { bins one = {1'b1}; }\n  endgroup\n";
  return text;
}

TEST(CheckerCovergroupReferences, ACheckerVariableClockingEventIsHonoured) {
  EXPECT_EQ(
      SortedOutput(Clocked("", "logic clk",
                           "  bit t = 0;\n"
                           "  always_ff @(posedge clk) t <= !t;\n" +
                               Counted("cg3", "t", 3) + Counted("cg4", "t", 4) +
                               "  cg3 i3 = new();\n  cg4 i4 = new();\n" +
                               Shown("edges", {"i3", "i4"}),
                           "  chk c(clk);\n")),
      (Lines{"edges 100 0"}));
}

TEST(CheckerCovergroupReferences, AnOutsideClockingEventIsHonoured) {
  std::string src =
      "package p;\n"
      "  bit pclk = 0;\n"
      "endpackage\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  always #5 p::pclk = ~p::pclk;\n"
      "  int mv5 = 5, mv6 = 6;\n"
      "  checker mchk;\n";
  src += Counted("cm5", "clk", 5);
  src += Counted("cm6", "clk", 6);
  src += Counted("cp5", "p::pclk", 5);
  src += Counted("cp6", "p::pclk", 6);
  src += Optioned("e5", "mv5");
  src += Optioned("e6", "mv6");
  src += "  cm5 m5 = new();\n  cm6 m6 = new();\n";
  src += "  cp5 p5 = new();\n  cp6 p6 = new();\n";
  src += "  e5 v5 = new();\n  e6 v6 = new();\n";
  src += Shown("outside", {"m5", "m6", "p5", "p6", "v5", "v6"});
  src +=
      "  endchecker\n"
      "  mchk u();\n"
      "  initial #52 $finish;\n"
      "endmodule\n";
  EXPECT_EQ(SortedOutput(src), (Lines{"outside 100 0 100 0 100 0"}));
}

TEST(CheckerCovergroupReferences, AGuardOrCrossNamingAFormalOrVariable) {
  EXPECT_EQ(
      SortedOutput(Clocked(
          "", "logic clk, a, off, on",
          "  bit t = 0, coff = 0, con = 1;\n"
          "  bit [3:0] cv = 0;\n"
          "  always_ff @(posedge clk) begin\n"
          "    t <= !t;\n"
          "    cv <= cv + 4'd1;\n"
          "  end\n" +
              Group("cg",
                    "    f0: coverpoint a iff (off) { bins one = {1'b1}; }\n"
                    "    f1: coverpoint a iff (on) { bins one = {1'b1}; }\n"
                    "    v0: coverpoint a iff (coff) { bins one = {1'b1}; }\n"
                    "    v1: coverpoint a iff (con) { bins one = {1'b1}; }\n"
                    "    ap: coverpoint a { bins one = {1'b1}; }\n"
                    "    tp: coverpoint t { bins lo = {1'b0}; "
                    "bins hi = {1'b1}; }\n"
                    "    cp: coverpoint cv { bins b[] = {[0:4]}; }\n"
                    "    x1: cross ap, tp;\n"
                    "    x4: cross ap, cp;\n"
                    "    xf: cross ap, tp iff (off);\n"
                    "    xv: cross ap, tp iff (coff);\n") +
              "  cg i = new();\n" +
              Shown("guards", {"i.f0", "i.f1", "i.v0", "i.v1", "i.x1", "i.x4",
                               "i.xf", "i.xv"}),
          "  logic a = 1, off = 0, on = 1;\n  chk c(clk, a, off, on);\n")),
      (Lines{"guards 0 100 0 100 100 100 0 0"}));
}

TEST(CheckerCovergroupReferences, DISABLED_AFormalInAnOptionTakesTheActual) {
  EXPECT_EQ(
      SortedOutput(Clocked(
          "", "logic clk, int n5, n6, k5, k6, wt, gl",
          Optioned("l5", "n5") + Optioned("l6", "n6") + Optioned("v5", "k5") +
              Optioned("v6", "k6") +
              Group("wcg",
                    "    option.goal = gl;\n"
                    "    hit: coverpoint 1'b1 { bins one = {1'b1}; "
                    "option.weight = wt; }\n"
                    "    miss: coverpoint 1'b1 { bins zero = {1'b0}; }\n") +
              "  l5 i1 = new();\n  l6 i2 = new();\n"
              "  v5 i3 = new();\n  v6 i4 = new();\n  wcg i5 = new();\n" +
              Shown("options", {"i1", "i2", "i3", "i4", "i5"}) +
              "  final $display(\"goal %0d\", i5.option.goal);\n",
          "  int five = 5, six = 6;\n  chk c(clk, 5, 6, five, six, 3, 77);\n")),
      (Lines{"goal 77", "options 100 0 100 0 75"}));
}

TEST(CheckerCovergroupReferences, AVariableInAnOptionTakesItsValue) {
  EXPECT_EQ(
      SortedOutput(Clocked("package p;\n"
                           "  int p5 = 5, p6 = 6;\n"
                           "endpackage\n",
                           "logic clk",
                           "  int c5 = 5, c6 = 6;\n" + Optioned("a5", "c5") +
                               Optioned("a6", "c6") + Optioned("q5", "p::p5") +
                               Optioned("q6", "p::p6") +
                               "  a5 i1 = new();\n  a6 i2 = new();\n"
                               "  q5 i5 = new();\n  q6 i6 = new();\n" +
                               Shown("vars", {"i1", "i2", "i5", "i6"}),
                           "  chk c(clk);\n")),
      (Lines{"vars 100 0 100 0"}));
}

}  // namespace
