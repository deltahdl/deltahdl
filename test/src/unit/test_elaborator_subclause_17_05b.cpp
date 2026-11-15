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

const char* const kTiming =
    "an initial procedure in checker 'chk' may use only an event control for "
    "timing; a delay, a cycle delay and a wait are not allowed";

const char* const kOffList =
    "this statement is none of those an initial procedure of checker 'chk' "
    "may hold";

const char* const kNotLet =
    "only a let declaration may stand in an initial procedure of checker "
    "'chk'";

std::string InitialChecker(const std::string& items) {
  return "package tp;\n"
         "  task automatic t(); endtask\n"
         "endpackage\n"
         "checker chk(logic a, clk, event e1, e2);\n"
         "  bit x, w;\n"
         "  bit arr [2];\n"
         "  sequence s; @(posedge clk) a; endsequence\n"
         "  default clocking cb @(posedge clk); output w; endclocking\n"
         "  function void vf(); endfunction\n" +
         items +
         "endchecker\n"
         "module top;\n"
         "  logic a, clk;\n"
         "  event e1, e2;\n"
         "  chk c(a, clk, e1, e2);\n"
         "endmodule\n";
}

void ExpectAccepted(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  EXPECT_EQ(f.diag.ErrorCount(), 0u) << src;
}

void ExpectEachReported(const std::string& src, const char* message,
                        const std::string& sub,
                        const std::vector<std::string>& markers,
                        const std::vector<std::string>& clean) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  for (const auto& marker : markers) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                              LineHolding(src, marker), sub))
        << marker;
  }
  for (const auto& marker : clean) {
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), LineHolding(src, marker)))
        << marker;
  }
}

TEST(CheckerInitialContents, EachEventControlFormIsAccepted) {
  ExpectAccepted(
      InitialChecker("  initial @(e1) a01: assert (a);\n"
                     "  initial @(posedge a or e1) a02: assert (a);\n"
                     "  initial @clk a03: assert (a);\n"
                     "  initial @(a, clk) a04: assert (a);\n"
                     "  initial @(posedge clk iff a) a05: assert (a);\n"
                     "  initial @(s) a06: assert (a);\n"
                     "  initial @(cb) a07: assert (a);\n"
                     "  initial @* a08: assert (a);\n"
                     "  initial @(*) a09: assert (a);\n"
                     "  initial @(posedge clk);\n"
                     "  initial @(e1) @(e2) a10: assert (a);\n"));
}

TEST(CheckerInitialContents, EachAssertionFormIsAccepted) {
  ExpectAccepted(InitialChecker(
      "  initial d01: assert #0 (a) vf(); else vf();\n"
      "  initial d02: assume #0 (a) vf(); else vf();\n"
      "  initial d03: cover #0 (a) vf();\n"
      "  initial d04: assert final (a) vf(); else vf();\n"
      "  initial d05: assume final (a) vf(); else vf();\n"
      "  initial d06: cover final (a) vf();\n"
      "  initial p01: assert property (@(posedge clk) a) vf(); else vf();\n"
      "  initial p02: assume property (@(posedge clk) a) vf(); else vf();\n"
      "  initial p03: cover property (@(posedge clk) a) vf();\n"
      "  initial p04: cover sequence (@(posedge clk) a) vf();\n"
      "  initial p05: restrict property (@(posedge clk) a);\n"));
}

TEST(CheckerInitialContents, LetDeclarationsAndBlocksAreAccepted) {
  ExpectAccepted(
      InitialChecker("  initial begin : b1\n"
                     "    let l1 = a;\n"
                     "    l01: assert (l1);\n"
                     "  end\n"
                     "  initial begin\n"
                     "    begin\n"
                     "      let l2 = a;\n"
                     "      @(e1) l02: assert (l2);\n"
                     "    end\n"
                     "  end\n"
                     "  initial begin end\n"));
}

TEST(CheckerInitialContents, EachOtherTimingControlIsReported) {
  ExpectEachReported(
      InitialChecker("  initial @(posedge a) t00: assert (a);\n"
                     "  initial ##1 t01: assert (a);\n"
                     "  initial @(posedge a) #1 t02: assert (a);\n"
                     "  initial wait (a) t03: assert (a);\n"
                     "  initial wait fork;\n"),
      kTiming, "17.5", {"t01:", "t02:", "t03:", "wait fork"}, {"t00:"});
}

TEST(CheckerInitialContents, DISABLED_AWaitOrderIsReported) {
  ExpectEachReported(InitialChecker("  initial @(e1) @(e2) w0: assert (a);\n"
                                    "  initial wait_order (e1, e2);\n"
                                    "  initial wait_order (e1, e2) w2: "
                                    "assert (a);\n"
                                    "  initial wait_order (e2, e1)\n"
                                    "    else vf();\n"
                                    "  initial w4: assert (a) else "
                                    "wait_order (e1, e2);\n"),
                     kTiming, "17.5",
                     {"initial wait_order (e1, e2);",
                      "w2:", "initial wait_order (e2, e1)", "w4:"},
                     {"w0:"});
}

TEST(CheckerInitialContents, EachStatementOffTheListIsReported) {
  ExpectEachReported(
      InitialChecker(
          "  initial s00: assert (a);\n"
          "  initial unique if (a) s01: assert (a);\n"
          "  initial unique0 if (a) s02: assert (a);\n"
          "  initial priority if (a) s03: assert (a);\n"
          "  initial case (a) 1'b1: s04: assert (a); endcase\n"
          "  initial casez (a) 1'b1: s05: assert (a); endcase\n"
          "  initial casex (a) 1'b1: s06: assert (a); endcase\n"
          "  initial case (a) inside 1'b1: s07: assert (a); endcase\n"
          "  initial case (a) matches 1'b1: s08: assert (a); endcase\n"
          "  initial unique case (a) 1'b1: s09: assert (a); endcase\n"
          "  initial unique0 case (a) 1'b1: s10: assert (a); endcase\n"
          "  initial priority case (a) 1'b1: s11: assert (a); endcase\n"
          "  initial for (int i = 0; i < 2; i++) s12: assert (a);\n"
          "  initial foreach (arr[i]) s13: assert (a);\n"
          "  initial while (a) s14: assert (a);\n"
          "  initial forever s15: assert (a);\n"
          "  initial repeat (2) s16: assert (a);\n"
          "  initial do s17: assert (a); while (a);\n"
          "  initial repeat (2) @(posedge clk);\n"
          "  initial return;\n"
          "  initial break;\n"
          "  initial continue;\n"
          "  initial x = 1;\n"
          "  initial x <= 1;\n"
          "  initial x++;\n"
          "  initial x += 1;\n"
          "  initial tp::t();\n"
          "  initial vf();\n"
          "  initial cb.w <= 1;\n"
          "  initial fork s18: assert (a); join\n"
          "  initial fork s19: assert (a); join_any\n"
          "  initial fork s20: assert (a); join_none\n"
          "  initial begin : db disable db; end\n"
          "  initial disable fork;\n"
          "  initial -> e1;\n"
          "  initial ->> e2;\n"
          "  initial assign x = 1;\n"
          "  initial deassign x;\n"
          "  initial force x = 1;\n"
          "  initial release x;\n"
          "  initial randcase 1: s21: assert (a); endcase\n"
          "  initial randsequence (m) m : { vf(); }; endsequence\n"
          "  initial expect (@(posedge clk) a);\n"),
      kOffList, "17.5",
      {"s01:",
       "s02:",
       "s03:",
       "s04:",
       "s05:",
       "s06:",
       "s07:",
       "s08:",
       "s09:",
       "s10:",
       "s11:",
       "s12:",
       "s13:",
       "s14:",
       "s15:",
       "s16:",
       "s17:",
       "repeat (2) @",
       "initial return;",
       "initial break;",
       "initial continue;",
       "initial x = 1;",
       "initial x <= 1;",
       "initial x++;",
       "initial x += 1;",
       "tp::t();",
       "initial vf();",
       "cb.w <= 1;",
       "s18:",
       "s19:",
       "s20:",
       "disable db;",
       "disable fork;",
       "-> e1;",
       "->> e2;",
       "assign x = 1;",
       "deassign x;",
       "force x = 1;",
       "release x;",
       "s21:",
       "randsequence",
       "expect ("},
      {"s00:"});
}

size_t CountOnLine(const std::vector<Diagnostic>& diags, const char* message,
                   uint32_t line) {
  size_t count = 0;
  for (const auto& d : diags) {
    if (d.loc.line == line && d.message.find(message) != std::string::npos) {
      ++count;
    }
  }
  return count;
}

TEST(CheckerInitialContents, DISABLED_AForLoopIsReportedOnce) {
  std::string src = InitialChecker(
      "  initial for (int i = 0; i < 2; i++) s12: assert (a);\n");
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  EXPECT_EQ(
      CountOnLine(f.diag.Diagnostics(), kOffList, LineHolding(src, "s12:")),
      1u);
}

TEST(CheckerInitialContents, DISABLED_ADeclarationOtherThanALetIsReported) {
  ExpectEachReported(
      InitialChecker("  initial begin let l0 = a; @(posedge a) n0: assert "
                     "(l0); end\n"
                     "  initial begin int y; @(posedge a) n1: assert (a); end\n"
                     "  initial begin typedef int t; @(posedge a) n2: assert "
                     "(a); end\n"
                     "  initial begin localparam int P = 1; @(posedge a) n3: "
                     "assert (a); end\n"),
      kNotLet, "17.5", {"n1:", "n2:", "n3:"}, {"n0:"});
}

const char* const kPlacedBody =
    "    initial $display(\"off\");\n"
    "    initial @(posedge clk) on: assert (clk);\n";

std::string PlacedChecker() {
  return std::string("  checker chk(logic clk);\n") + kPlacedBody +
         "  endchecker\n";
}

TEST(CheckerInitialContents, EachPlaceOfTheCheckerIsChecked) {
  const std::string kModule = "module top;\n  logic clk;\n";
  for (const std::string& src :
       {kModule + PlacedChecker() + "  chk c(clk);\nendmodule\n",
        "package pk;\n" + PlacedChecker() + "endpackage\n" + kModule +
            "  pk::chk c(clk);\nendmodule\n",
        "interface ifc(input logic clk);\n" + PlacedChecker() +
            "  chk c(clk);\nendinterface\n" + kModule +
            "  ifc i(clk);\nendmodule\n",
        "program prg(input logic clk);\n" + PlacedChecker() +
            "  chk c(clk);\nendprogram\n" + kModule +
            "  prg p(clk);\nendmodule\n",
        "checker outer(logic clk);\n" + PlacedChecker() +
            "  chk c(clk);\nendchecker\n" + kModule +
            "  outer o(clk);\nendmodule\n"}) {
    ExpectEachReported(src, kOffList, "17.5", {"$display(\"off\")"}, {"on:"});
  }
}

TEST(CheckerInitialContents, EachGenerateBlockOfTheCheckerIsChecked) {
  std::string src =
      "checker chk(logic clk);\n"
      "  if (1) begin : g1\n"
      "    initial $display(\"if\");\n"
      "    initial @(posedge clk) o1: assert (clk);\n"
      "  end else begin : g2\n"
      "    initial $display(\"else\");\n"
      "    initial @(posedge clk) o2: assert (clk);\n"
      "  end\n"
      "  for (genvar i = 0; i < 1; i++) begin : g3\n"
      "    initial $display(\"for\");\n"
      "    initial @(posedge clk) o3: assert (clk);\n"
      "  end\n"
      "  case (1)\n"
      "    1: begin : g4\n"
      "      initial $display(\"case\");\n"
      "      initial @(posedge clk) o4: assert (clk);\n"
      "    end\n"
      "  endcase\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk;\n"
      "  chk c(clk);\n"
      "endmodule\n";
  ExpectEachReported(src, kOffList, "17.5",
                     {"$display(\"if\")", "$display(\"else\")",
                      "$display(\"for\")", "$display(\"case\")"},
                     {"o1:", "o2:", "o3:", "o4:"});
}

}  // namespace
