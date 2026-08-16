#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_input_sweep.h"

using namespace delta;

namespace {

// What §12.5.4 `case ... inside` lowers to. Every case drives the module's
// input through the netlist and reads the output word, because a netlist whose
// every output bit is constant zero is what a missing lowering produces and
// `ASSERT_NE(aig, nullptr)` holds over it.

// §12.5.4 rules that a case item written `[expr:expr]` matches the
// case_expression when it lies within the bounds inclusive, so sel 1 and sel 2
// both select the second item. The netlist drives y = 0 there instead: the
// parser builds a range item as a baseless `ExprKind::kSelect`, and the bit
// lowering answers constant false at every position of it, so the item compares
// equal only where the selector is zero and the default arm takes every other
// value.
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

// §12.5.4 rules that a case item written `[expr:expr]` matches only the
// case_expression values within its bounds, so sel 0 and sel 3 through 7 reach
// the default arm. The case above passes a lowering that answers a range item
// true at every value, and this one fails it. The netlist drives y = 1 at sel 1
// and sel 2 today, for the same reason: the parser builds a range item as a
// baseless `ExprKind::kSelect`, and the bit lowering answers constant false at
// every position of it, so the item compares equal only where the selector is
// zero.
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

// §12.5.4 rules that "the inside operator uses asymmetric wildcard matching
// (see 11.4.6)", and that "the case_expression shall be the left operand, and
// each case_item_expression shall be the right operand", so a `?` in the item
// masks that bit position and a bit of the selector never masks anything. The
// subclause's own example gives `3'b0?0` as matching `'b000 'b010 'b0x0 'b0z0`,
// and a netlist carries no x or z on an input, so 0 and 2 are the reachable
// matches. A lowering that read the wildcard off the selector instead would
// answer y = 2 at every value.
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
