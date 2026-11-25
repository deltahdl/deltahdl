#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr char kLeaf[] =
    "module leaf(input [7:0] a, output int o); assign o = a + 1; endmodule\n";

struct SpecparamRead {
  const char* items;
  const char* printed;
};

std::string Shown(const std::string& declaration, const std::string& items) {
  SimFixture f;
  return RunCapture(std::string(kLeaf) +
                        "module top;\n  logic [15:0] v = 16'h1234;\n  int x;\n"
                        "  wire [31:0] y;\n  " +
                        declaration + "\n  " + items + "\nendmodule\n",
                    f);
}

constexpr SpecparamRead kReads[] = {
    {"assign y = sp; initial #1 $display(\"%0d\", y);", "7\n"},
    {"wire [7:0] w = sp + 1; initial #1 $display(\"%0d\", w);", "8\n"},
    {"initial begin x = sp + 1; $display(\"%0d\", x); end", "8\n"},
    {"initial begin x <= sp; #1 $display(\"%0d\", x); end", "7\n"},
    {"initial begin x = 1; x += sp; $display(\"%0d\", x); end", "8\n"},
    {"int i = sp * 2; initial $display(\"%0d\", i);", "14\n"},
    {"always_comb x = sp - 1; initial #1 $display(\"%0d\", x);", "6\n"},
    {"function int f(int a); return a + sp; endfunction"
     " initial $display(\"%0d\", f(2));",
     "9\n"},
    {"function int f(int a = sp); return a; endfunction"
     " initial $display(\"%0d\", f());",
     "7\n"},
    {"task t(); #sp x = sp; endtask"
     " initial begin t(); $display(\"%0d %0d\", x, $time); end",
     "7 7\n"},
    {"class C; int p = sp; function int f(); return p + sp; endfunction"
     " endclass initial begin C c; c = new; $display(\"%0d\", c.f()); end",
     "14\n"},
    {"if (1) begin : g initial $display(\"%0d\", sp); end", "7\n"},
    {"leaf u(.a(sp), .o(y)); initial #1 $display(\"%0d\", y);", "8\n"},
    {"initial case (7) sp: $display(\"hit\"); default: $display(\"miss\");"
     " endcase",
     "hit\n"},
    {"initial begin repeat (sp) x++; $display(\"%0d\", x); end", "7\n"},
    {"initial $display(\"%0d\", sp > 6 ? 1 : 2);", "1\n"},
    {"initial $display(\"%0d\", {1'b1, sp[2:0]});", "15\n"},
    {"initial $display(\"%h %h\", v[sp:0], v[sp]);", "34 0\n"},
    {"initial $display(\"%h\", v[4+:sp]);", "23\n"},
    {"initial $display(\"%h\", v[10-:sp]);", "23\n"},
    {"initial $display(\"%b\", {sp{1'b1}});", "1111111\n"},
    {"initial $display(\"%0d\", $bits({sp{2'b01}}));", "14\n"},
    {"wire [15:0] w = {sp{2'b01}}; initial #1 $display(\"%h\", w);", "1555\n"},
    {"initial $display(\"%0d\", sp'(v));", "52\n"},
    {"initial $display(\"%0d\", 5 inside {[1:sp]});", "1\n"},
    {"let l(a) = a + sp; initial $display(\"%0d\", l(1));", "8\n"},
    {"initial assert (sp == 7) $display(\"pass\");", "pass\n"},
    {"if (sp > 6) begin : g initial $display(\"then\"); end"
     " else begin : h initial $display(\"else\"); end",
     "then\n"},
    {"if (sp > 7) begin : g initial $display(\"then\"); end"
     " else if (sp == 7) begin : h initial $display(\"elsif\"); end",
     "elsif\n"},
    {"if (sp[1:0] == 3) begin : g initial $display(\"select\"); end",
     "select\n"},
    {"case (sp) 6: begin : g initial $display(\"six\"); end"
     " 7: begin : h initial $display(\"seven\"); end endcase",
     "seven\n"},
    {"case (7) sp - 1: begin : g initial $display(\"six\"); end"
     " sp: begin : h initial $display(\"item\"); end endcase",
     "item\n"},
    {"for (genvar i = 5; i < sp; i++) begin : g"
     " initial $display(\"%0d\", i); end",
     "5\n6\n"},
    {"for (genvar i = sp; i < 8; i++) begin : g"
     " initial $display(\"%0d\", i); end",
     "7\n"},
    {"for (genvar i = 0; i < 8; i = i + sp) begin : g"
     " initial $display(\"%0d\", i); end",
     "0\n7\n"},
    {"if (1) begin : o if (sp == 7) begin : g initial $display(\"nested\");"
     " end end",
     "nested\n"},
    {"for (genvar i = 0; i < 1; i++) begin : o"
     " if (sp + i == 7) begin : g initial $display(\"looped\"); end end",
     "looped\n"},
    {"wire [31:0] aa; alias y[sp:0] = aa[sp:0]; assign y = 32'h15a;"
     " initial #1 $display(\"%h\", aa[8:0]);",
     "z5a\n"},
    {"pullup (y[sp]); initial #1 $display(\"%b\", y[7:6]);", "1z\n"},
    {"assign y[0+:sp] = 7'h55; initial #1 $display(\"%b\", y[7:0]);",
     "z1010101\n"},
    {"function int f(int a); return a; endfunction if (f(sp) == 7) begin : g"
     " initial $display(\"yes\"); end",
     "yes\n"},
    {"for (genvar i = 0; i < 8; i++) begin : g int k = i; end"
     " initial #1 $display(\"%0d\", g[sp].k);",
     "7\n"},
    {"logic [7:0] r; always_comb r[sp] = 1; always_comb r[6] = 0;"
     " initial #1 $display(\"%b\", r[7:6]);",
     "10\n"},
    {"bit [7:0] r [8]; always_comb r[sp] = 1; always_comb r[6] = 0;"
     " initial #1 $display(\"%0d\", r[7]);",
     "1\n"},
    {"bit n; logic [7:0] d; clocking cb @(posedge n); output #sp d;"
     " endclocking initial #5 n = 1; initial begin @(cb); cb.d <= 8;"
     " #6 $display(\"%0d\", d); #2 $display(\"%0d\", d); end",
     "x\n8\n"},
    {"if (1) begin : g localparam sp = 2; initial $display(\"%b\","
     " {sp{1'b1}}); end",
     "11\n"},
};

constexpr char kClocked[] =
    "bit n; int cnt, cyc; initial repeat (12) begin #5 n = 1; #5 n = 0; end"
    " always @(posedge n) cyc <= cyc + 1;"
    " initial #200 $display(\"%0d\", cnt); ";

constexpr SpecparamRead kClockedReads[] = {
    {"a1: assert property (@(posedge n) ##sp 1) cnt++;", "5\n"},
    {"a1: assert property (@(posedge n) 1[*sp]) cnt++;", "6\n"},
    {"a1: assert property (@(posedge n) nexttime[sp] 1) cnt++;", "5\n"},
    {"a1: assert property (@(posedge n) always[0:sp] 1) cnt++;", "5\n"},
    {"a1: assert property (@(posedge n) s_eventually[sp:sp] 1) cnt++;", "5\n"},
    {"sequence s; int i; (1, i = 0) ##1 (1, i[sp] = 1) ##1 i == 128;"
     " endsequence a1: assert property (@(posedge n) s) cnt++;",
     "10\n"},
    {"always @(posedge n) if (cyc == 8) cnt = $past(cyc, sp);", "1\n"},
};

TEST(SpecparamReads, SpecparamBoundsAnAssertion) {
  for (const char* declaration :
       {"specparam sp = 7;", "specify specparam sp = 7; endspecify",
        "specparam [2:0] sp = 15;"}) {
    for (const SpecparamRead& read : kClockedReads) {
      SCOPED_TRACE(std::string(declaration) + " " + read.items);
      EXPECT_EQ(Shown(declaration, std::string(kClocked) + read.items),
                read.printed);
    }
  }
}

TEST(SpecparamReads, SpecparamHidesAParameterOfTheCompilationUnit) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("parameter sp = 9;\n"
                 "module top; specparam sp = 3;\n"
                 "  if (sp == 3) begin : g initial $display(\"own\"); end\n"
                 "  else begin : h initial $display(\"unit\"); end\n"
                 "  initial #1 $display(\"%b\", {sp{1'b1}});\n"
                 "endmodule\n",
                 f),
      "own\n111\n");
}

TEST(SpecparamReads, ModuleBodySpecparamIsReadAsAValue) {
  for (const SpecparamRead& read : kReads) {
    SCOPED_TRACE(read.items);
    EXPECT_EQ(Shown("specparam sp = 7;", read.items), read.printed);
  }
}

TEST(SpecparamReads, SpecifyBlockSpecparamIsReadAsAValue) {
  for (const SpecparamRead& read : kReads) {
    SCOPED_TRACE(read.items);
    EXPECT_EQ(Shown("specify specparam sp = 7; endspecify", read.items),
              read.printed);
  }
}

TEST(SpecparamReads, RangedSpecparamIsReadCutToItsRange) {
  for (const char* declaration :
       {"specparam [2:0] sp = 15;", "specparam [0:2] sp = 15;",
        "specify specparam [2:0] sp = 15; endspecify"}) {
    for (const SpecparamRead& read : kReads) {
      const std::string kItems = read.items;
      if (kItems.find("sp - 1") != std::string::npos ||
          kItems.find("[2:0]") != std::string::npos ||
          kItems.find("[1:0]") != std::string::npos ||
          kItems.find("sp * 2") != std::string::npos ||
          kItems.find("sp + 1") != std::string::npos) {
        continue;
      }
      SCOPED_TRACE(std::string(declaration) + " " + kItems);
      EXPECT_EQ(Shown(declaration, kItems), read.printed);
    }
  }
}

TEST(SpecparamReads, SpecparamSetFromAParameterSelectsAGenerateBlock) {
  EXPECT_EQ(Shown("parameter P = 3; specparam b = P + 1, sp = b * 2;",
                  "if (sp == 8) begin : g initial $display(\"eight\"); end"
                  " initial #1 $display(\"%b\", {sp{1'b1}});"),
            "eight\n11111111\n");
}

TEST(SpecparamReads, RangeBoundedByAParameterCutsTheValue) {
  EXPECT_EQ(Shown("parameter P = 2; specparam [P:0] sp = 15;",
                  "if (sp == 7) begin : g initial $display(\"cut\"); end"
                  " initial #1 $display(\"%0d %0d\", sp, $bits(sp));"),
            "cut\n7 3\n");
}

TEST(SpecparamReads, RangeWiderThanAnIntegerKeepsTheValue) {
  EXPECT_EQ(Shown("specparam [70:0] sp = 15;",
                  "if (sp == 15) begin : g initial $display(\"whole\"); end"
                  " initial #1 $display(\"%0d %0d\", sp, $bits(sp));"),
            "whole\n15 71\n");
}

constexpr SpecparamRead kRangeless[] = {
    {"specparam a = 8'd200, sp = a;", "200 8\n"},
    {"parameter a = 8'd200; specparam sp = a;", "200 8\n"},
    {"specparam a = 8'd200, sp = a + 8'd100;", "44 8\n"},
    {"specparam a = 8'd200, sp = {a, a};", "51400 16\n"},
    {"specparam a = 8'd200, sp = a[3:0];", "8 4\n"},
    {"specparam a = 8'd200, sp = 1 ? a : a;", "200 8\n"},
    {"specparam sp = -1;", "-1 32\n"},
    {"specparam sp = 8'sd200;", "-56 8\n"},
    {"specparam a = -1, sp = a;", "-1 32\n"},
    {"specparam sp = 40'hff_ffff_ffff;", "1099511627775 40\n"},
    {"specparam [7:0] sp = -1;", "255 8\n"},
    {"specparam [7:0] sp = 2.5;", "3 8\n"},
    {"specparam a = 2.5; specparam [7:0] sp = a;", "3 8\n"},
};

TEST(SpecparamReads, RangelessSpecparamTakesTheRangeOfItsValue) {
  for (const SpecparamRead& read : kRangeless) {
    SCOPED_TRACE(read.items);
    EXPECT_EQ(
        Shown(read.items, "initial $display(\"%0d %0d\", sp, $bits(sp));"),
        read.printed);
  }
}

TEST(SpecparamReads, SpecparamTakesTheRealValueOfAnotherConstant) {
  for (const char* declarations :
       {"specparam a = 1.5, sp = a;", "parameter a = 1.5; specparam sp = a;",
        "specparam a = 0.5, sp = a + 1;",
        "specify specparam a = 1.5; specparam sp = a; endspecify"}) {
    SCOPED_TRACE(declarations);
    EXPECT_EQ(Shown(declarations, "initial $display(\"%f\", sp);"),
              "1.500000\n");
  }
}

TEST(SpecparamReads, SpecparamOfALaterSpecifyBlockKeepsItsRange) {
  EXPECT_EQ(Shown("if ({1'b1, sp} == 9'd456) begin : g"
                  " initial $display(\"hit\"); end",
                  "specify specparam a = 8'd200; specparam sp = a; endspecify"),
            "hit\n");
}

TEST(SpecparamReads, RealSpecparamIsReadAsAValue) {
  EXPECT_EQ(Shown("specparam sp = 1.5;",
                  "initial begin $display(\"%0.2f\", sp * 2);"
                  " x = sp; $display(\"%0d\", x); end"),
            "3.00\n2\n");
}

TEST(SpecparamReads, SpecparamIsReadThroughAHierarchicalName) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module c; specparam sp = 3;"
                 " specify specparam sq = 4; endspecify endmodule\n"
                 "module top; c u(); wire [7:0] w = u.sp;\n"
                 "  initial #1 $display(\"%0d %0d %0d\", u.sp, top.u.sq, w);\n"
                 "endmodule\n",
                 f),
      "3 4 3\n");
}

}  // namespace
