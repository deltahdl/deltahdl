#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

size_t Occurrences(const std::string& text, std::string_view needle) {
  size_t count = 0;
  for (size_t at = text.find(needle); at != std::string::npos;
       at = text.find(needle, at + needle.size())) {
    ++count;
  }
  return count;
}

// The stimulus both window checkers run under: posedges every 10 from 5, the
// signals driven at negedges. A window opens at the posedge at 15 and closes
// at 45 with the test expression true throughout; a second opens at 75, the
// test expression falls at 95 and the window closes at 105.
constexpr std::string_view kStimulus =
    "  logic clk = 0, rst = 0, s = 0, e = 0, t = 1;\n"
    "  always #5 clk = ~clk;\n"
    "  default clocking @(posedge clk); endclocking\n"
    "  default disable iff rst;\n"
    "  initial begin\n"
    "    #10 s = 1; #10 s = 0;\n"
    "    #20 e = 1; #10 e = 0;\n"
    "    #20 s = 1; #10 s = 0;\n"
    "    #10 t = 0;\n"
    "    #10 e = 1; #10 e = 0;\n"
    "    #20 $finish;\n"
    "  end\n";

// §17.9: a checker that requires an expression to hold over each window
// between two Boolean events: untyped event formals, the clock and reset
// defaulting to $inferred_clock and $inferred_disable, a string formal, an
// enumeration formal a generate if tests, default clocking and default
// disable iff in the checker, and the window kept in checker variables an
// always_comb and an always_ff drive. Its assertion holds over the first
// window and fails at 95 in the second, and each cover reports both.
TEST(ComplexChecker, ABooleanWindowCheckerRunsAsTheClauseDescribes) {
  SimFixture f;
  std::string out = RunCapture(
      "typedef enum { lvl_none, lvl_all } cov_lvl_t;\n"
      "checker window_bool(logic cond, untyped open_ev, untyped close_ev,\n"
      "                    event ck = $inferred_clock,\n"
      "                    logic rs = $inferred_disable,\n"
      "                    string msg = \"window broken\",\n"
      "                    cov_lvl_t lvl = lvl_all);\n"
      "  default clocking @ck; endclocking\n"
      "  default disable iff rs;\n"
      "  bit open = 1'b0, next_open = 1'b1;\n"
      "  always_comb begin\n"
      "    if (rs || open && close_ev) next_open = 1'b0;\n"
      "    else if (!open && open_ev) next_open = 1'b1;\n"
      "    else next_open = open;\n"
      "  end\n"
      "  always_ff @ck open <= next_open;\n"
      "  property p_win;\n"
      "    open_ev && !open |=> cond[+] ##0 close_ev;\n"
      "  endproperty\n"
      "  a_win: assert property (p_win) else $error(msg);\n"
      "  generate if (lvl != lvl_none) begin : cov\n"
      "    c_open: cover property (open_ev && !open) $display(\"opened\");\n"
      "    c_win: cover property (open_ev && !open\n"
      "      ##1 (!close_ev && open) [*] ##1 close_ev && open)\n"
      "      $display(\"spanned\");\n"
      "  end endgenerate\n"
      "endchecker\n"
      "module top;\n" +
          std::string(kStimulus) +
          "  window_bool w(t, s, e);\n"
          "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(Occurrences(out, "opened"), 2u);
  EXPECT_EQ(Occurrences(out, "spanned"), 2u);
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "window broken");
  EXPECT_EQ(f.ctx.LastSeverityTime().ticks, 95u);
}

}  // namespace
