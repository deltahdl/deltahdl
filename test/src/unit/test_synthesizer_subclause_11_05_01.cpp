#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_input_sweep.h"

using namespace delta;

namespace {

// Every case below fails on a netlist whose every output bit is constant zero,
// which is what the synthesizer answers for a select today:
// `SynthLower::LowerExprBit` at src/synthesizer/synth_lower.cpp:505 has no
// `ExprKind::kSelect` arm and ends `default: return AigGraph::kConstFalse;`,
// and `SynthLower::LowerContAssign` at src/synthesizer/synth_lower.cpp:530 and
// `SynthLower::LowerAssignStmt` at src/synthesizer/synth_lower.cpp:696 both
// return early when the target is not `ExprKind::kIdentifier`.
//
// Every declaration below has a low bound other than zero, deliberately.
// §11.5.1 rules that "The actual bit that is accessed by an address is, in
// part, determined by the declaration", and in a vector declared `[N:0]` an
// index and a storage offset are the same number. A lowering that used an
// index as a storage offset would pass every `[N:0]` case whether it read the
// declaration or not.

// The test fails on any lowering that builds nothing for a bit-select, since
// this is the first case. It also fails a lowering that takes index 3 as
// storage offset 3, because §11.5.1 resolves index 3 against the declaration
// `[8:1]` to storage offset 2.
TEST(VectorSelect, BitSelectResolvesTheIndexAgainstTheDeclaredRange) {
  ExpectInputSweep(
      "module m(input [8:1] data, output y);\n"
      "  assign y = data[3];\n"
      "endmodule\n",
      256, [](uint64_t data) { return (data >> 2) & 1u; });
}

// The test fails on a lowering that subtracts the low bound whatever the
// direction of the declaration, which the case above passes. §11.5.1's own
// example is that `logic [15:0] acc;` and `logic [2:17] acc;` make one value of
// an index reach a different bit. In `[1:8]` index 1 is the most significant
// end, so index 3 is storage offset 5.
TEST(VectorSelect, BitSelectOfAnAscendingVectorReachesTheOppositeEnd) {
  ExpectInputSweep(
      "module m(input [1:8] data, output y);\n"
      "  assign y = data[3];\n"
      "endmodule\n",
      256, [](uint64_t data) { return (data >> 5) & 1u; });
}

// The test fails on a lowering that reaches a bit-select and builds nothing for
// a part-select. Such a lowering is passed by
// VectorSelect.BitSelectResolvesTheIndexAgainstTheDeclaredRange and by
// VectorSelect.BitSelectOfAnAscendingVectorReachesTheOppositeEnd, which each
// address one bit. §11.5.1 gives the part-select its own form, and `data[8:5]`
// under the declaration `[8:1]` addresses storage offsets 4 through 7.
TEST(VectorSelect, NonIndexedPartSelectCarriesTheAddressedBits) {
  ExpectInputSweep(
      "module m(input [8:1] data, output [3:0] y);\n"
      "  assign y = data[8:5];\n"
      "endmodule\n",
      256, [](uint64_t data) { return (data >> 4) & 0xFu; });
}

// The test fails on a lowering that treats `[base +: width]` as the range
// `[base : base - width + 1]`. §11.5.1 rules the indexed part-select selects
// `width_expr` bits starting at the base and ascending the bit range, so
// `data[2+:4]` addresses indices 2 through 5.
TEST(VectorSelect, IndexedPartSelectPlusAscendsFromItsBase) {
  ExpectInputSweep(
      "module m(input [8:1] data, output [3:0] y);\n"
      "  assign y = data[2+:4];\n"
      "endmodule\n",
      256, [](uint64_t data) { return (data >> 1) & 0xFu; });
}

// The test fails on a lowering that gives `-:` the same direction as `+:`,
// which VectorSelect.IndexedPartSelectPlusAscendsFromItsBase passes. §11.5.1
// rules that the `-:` form starts at the base and descends the bit range, so
// `data[8-:4]` addresses indices 5 through 8.
TEST(VectorSelect, IndexedPartSelectMinusDescendsFromItsBase) {
  ExpectInputSweep(
      "module m(input [8:1] data, output [3:0] y);\n"
      "  assign y = data[8-:4];\n"
      "endmodule\n",
      256, [](uint64_t data) { return (data >> 4) & 0xFu; });
}

// The test fails on a lowering that resolves a select against a port's
// declaration and not a net's. A port and a net record their declaration by
// different fields of the elaborator's RTLIR, so a fix that reads one and not
// the other passes the five cases above and fails here. §11.5.1 makes the
// declaration decide the bit an address reaches whichever object declares it.
TEST(VectorSelect, SelectOfAnInternalNetResolvesAgainstItsDeclaration) {
  ExpectInputSweep(
      "module m(input [7:0] a, output y);\n"
      "  wire [8:1] w;\n"
      "  assign w = a;\n"
      "  assign y = w[3];\n"
      "endmodule\n",
      256, [](uint64_t a) { return (a >> 2) & 1u; });
}

// The test fails on a lowering that drops a continuous assignment whose target
// is a select, which every case above writes its select on the right-hand side
// and so does not reach. It also fails a lowering that lets either assignment
// overwrite the bits the other drives: §11.5.1 part-selects address contiguous
// bits, and the two assignments here address disjoint runs of the same output.
TEST(VectorSelect, ContinuousAssignToAPartSelectWritesOnlyThoseBits) {
  ExpectInputSweep(
      "module m(input [3:0] a, output [8:1] y);\n"
      "  assign y[8:5] = a;\n"
      "  assign y[4:1] = ~a;\n"
      "endmodule\n",
      16, [](uint64_t a) { return ((a & 0xFu) << 4) | (~a & 0xFu); });
}

// The test fails on the same gap as
// VectorSelect.ContinuousAssignToAPartSelectWritesOnlyThoseBits, reached
// through a procedural assignment inside `always_comb` instead. That case does
// not reach it, because a continuous assignment and a procedural one are
// lowered by different functions. The `y = 8'b0;` ahead of the bit-select is
// what makes the other seven bits of `y` state a value the netlist owes.
TEST(VectorSelect, ProceduralAssignToABitSelectWritesOnlyThatBit) {
  ExpectInputSweep(
      "module m(input a, output logic [8:1] y);\n"
      "  always_comb begin\n"
      "    y = 8'b0;\n"
      "    y[3] = a;\n"
      "  end\n"
      "endmodule\n",
      2, [](uint64_t a) { return a != 0 ? uint64_t{4} : uint64_t{0}; });
}

// The test fails on the same gap as
// VectorSelect.NonIndexedPartSelectCarriesTheAddressedBits, without the source
// naming a select. The elaborator rewrites a concatenation on the left of a
// continuous assignment into one assignment per named target whose right-hand
// side is a part-select it builds, so this module reaches the synthesizer as
// two selects.
TEST(VectorSelect, ConcatenationLvalueSplitLowersItsPartSelects) {
  ExpectInputSweep(
      "module m(input [7:0] word, output [3:0] hi, output [3:0] lo);\n"
      "  assign {hi, lo} = word;\n"
      "endmodule\n",
      256, [](uint64_t word) {
        return ((word >> 4) & 0xFu) | ((word & 0xFu) << 4);
      });
}

// The test fails on a lowering that resolves only an index it can fold, which
// every case above passes because each writes its index as a literal. §11.5.1
// rules that a bit-select "can be addressed using an expression that shall be
// evaluated in a self-determined context", so `s` reaching the netlist as a
// port is a bit-select the standard defines. Such a select chooses among the
// bits of `data` rather than renaming them, and the four values of `s` name the
// four indices 5 through 8, which are storage offsets 4 through 7 under the
// declaration `[8:1]`. Bit 0 to 7 of the driven word is `data` and bit 8 to 9
// is `s`, in the order the ports are declared.
TEST(VectorSelect, BitSelectByAVariableIndexChoosesAmongTheBits) {
  ExpectInputSweep(
      "module m(input [8:1] data, input [1:0] s, output y);\n"
      "  assign y = data[s + 5];\n"
      "endmodule\n",
      1024, [](uint64_t v) {
        uint64_t data = v & 0xFFu;
        uint64_t s = (v >> 8) & 0x3u;
        return (data >> (4 + s)) & 1u;
      });
}

// The test fails on a lowering that reaches a bit-select by a variable index
// and builds nothing for an indexed part-select by one, which
// VectorSelect.BitSelectByAVariableIndexChoosesAmongTheBits passes. §11.5.1
// rules that "The lsb_base_expr and msb_base_expr can vary at run time" while
// the width "shall be a positive constant integer expression", so this is the
// form the subclause writes `dword[8*sel +: 8]` in. The two bits addressed are
// the indices `s + 3` and `s + 4`, which are storage offsets `s + 2` and
// `s + 3`.
TEST(VectorSelect, IndexedPartSelectByAVariableBaseAscendsFromIt) {
  ExpectInputSweep(
      "module m(input [8:1] data, input [1:0] s, output [1:0] y);\n"
      "  assign y = data[s + 3 +: 2];\n"
      "endmodule\n",
      1024, [](uint64_t v) {
        uint64_t data = v & 0xFFu;
        uint64_t s = (v >> 8) & 0x3u;
        return (data >> (s + 2)) & 0x3u;
      });
}

}  // namespace
