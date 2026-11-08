#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_input_sweep.h"

using namespace delta;

namespace {

TEST(CaseInsideStatementSynth, RangeItemSelectsEveryValueBetweenItsBounds) {
  ExpectInputSweep(
      "module m(input logic [1:0] sel, output logic [1:0] y);\n"
      "  always_comb begin\n"
      "    case (sel) inside\n"
      "      2'b00: y = 2'b01;\n"
      "      [2'b01:2'b10]: y = 2'b10;\n"
      "      default: y = 2'b00;\n"
      "    endcase\n"
      "  end\n"
      "endmodule",
      4, [](uint64_t sel) -> uint64_t {
        if (sel == 0) return 1;
        if (sel == 1 || sel == 2) return 2;
        return 0;
      });
}

TEST(CaseInsideStatementSynth, RangeItemDoesNotSelectAValueOutsideItsBounds) {
  ExpectInputSweep(
      "module m(input logic [2:0] sel, output logic [1:0] y);\n"
      "  always_comb begin\n"
      "    case (sel) inside\n"
      "      [3'd1:3'd2]: y = 2'b10;\n"
      "      default: y = 2'b01;\n"
      "    endcase\n"
      "  end\n"
      "endmodule",
      8, [](uint64_t sel) -> uint64_t {
        return (sel == 1 || sel == 2) ? uint64_t{2} : uint64_t{1};
      });
}

TEST(CaseInsideStatementSynth, WildcardItemMatchesUnderAsymmetricMatching) {
  ExpectInputSweep(
      "module m(input logic [2:0] sel, output logic [1:0] y);\n"
      "  always_comb begin\n"
      "    case (sel) inside\n"
      "      3'b0?0: y = 2'b10;\n"
      "      default: y = 2'b01;\n"
      "    endcase\n"
      "  end\n"
      "endmodule",
      8, [](uint64_t sel) -> uint64_t {
        return (sel == 0 || sel == 2) ? uint64_t{2} : uint64_t{1};
      });
}

}  // namespace
