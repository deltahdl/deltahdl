#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// The synthesizer's answer for a §11.5.1 select, held against the simulator's
// answer for the same module. Each case drives one input word through the
// netlist `SynthLower::Lower` builds and through a simulation of the same
// module, and asserts the two output words are equal.
//
// The two components resolved §11.5.1's index-to-offset rule from separate
// copies of one type: `PackedRange` in the simulator, and `DeclaredPackedRange`
// in the elaborator, which is the copy the synthesizer read. A correction to
// either copy left the other answering a declaration differently. No case
// caught that, because a case written over one component asserts its answer
// against a literal and passes on that component's own copy;
// test/src/unit/test_synthesizer_subclause_11_05_01a.cpp is the file of such
// cases for the synthesizer. The cases here assert the two components against
// each other, so a correction applied to one and not to the other fails them.
//
// The same commit replaces both copies with one definition in
// src/common/packed_range.h. These cases do not rest on that: they compare the
// two answers and name neither, so they keep failing on any later divergence
// however the rule comes to be written.
//
// Every declaration below has a low bound other than zero. §11.5.1 rules that
// "The actual bit that is accessed by an address is, in part, determined by the
// declaration", and in a vector declared `[N:0]` an index and a storage offset
// are the same number. A case declared `[N:0]` passes whether either component
// read the declaration or not.

// Drive `input_word` into the module that `data_range`, `y_range` and
// `select_expr` describe, once through the netlist the synthesizer builds for
// it and once through a simulation of it, and expect the two output words to be
// equal.
//
// The module text is built once and handed to both components. The synthesizer
// takes it as the top module, because `SynthLower::MapPorts` allocates one AIG
// input per bit of an input port and `EvalAigOutputs` drives those inputs. The
// simulator takes it beneath a module `top` that drives `data` from a wire and
// reads `y` into one, because a simulation drives no port of the module it
// runs.
//
// Bit i of `input_word` is bit i of the input port's storage in both
// components. lib/cpp/test_helpers/helpers_synth_input_sweep.h records that
// `SynthLower::MapPorts` emits an input port's bits low bit first, and `drv` is
// declared with the range `data` is declared with, so the port connection
// carries each storage bit to the bit at the same position. Bit j of each
// answer is bit j of the output port's storage for the same reason.
//
// `data` is eight bits wide in every case below, which is the width the
// driver's literal is written to.
void ExpectSelectAgrees(const std::string& data_range,
                        const std::string& y_range,
                        const std::string& select_expr, uint64_t input_word) {
  std::string dut = "module m(input " + data_range + " data, output " +
                    y_range + " y);\n  assign y = " + select_expr +
                    ";\nendmodule\n";
  SCOPED_TRACE(dut);
  SCOPED_TRACE("input word " + std::to_string(input_word));

  SynthFixture synth_fixture;
  const auto* mod = ElaborateSrc(synth_fixture, dut);
  ASSERT_NE(mod, nullptr);
  SynthLower synth(synth_fixture.arena, synth_fixture.diag);
  const auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  uint64_t synthesized = EvalAigOutputs(*aig, input_word);

  std::string tb = dut + "module top;\n  wire " + data_range +
                   " drv;\n  wire " + y_range + " result;\n" +
                   "  assign drv = 8'd" + std::to_string(input_word) +
                   ";\n  m u(.data(drv), .y(result));\nendmodule\n";
  SimFixture sim_fixture;
  auto* simulated = RunAndFindVar(tb, sim_fixture, "result");
  ASSERT_NE(simulated, nullptr);
  EXPECT_EQ(synthesized, simulated->value.ToUint64());
}

// The case fails when one component resolves index 3 against the declaration
// `[8:1]` and the other takes index 3 as storage offset 3. §11.5.1 makes the
// declaration decide which bit an address reaches, and the driven word 8'hA5
// carries 1 at storage offset 2 and 0 at storage offset 3, so the two
// resolutions answer differently. This is the first case, so it also fails when
// either component builds nothing for a bit-select.
TEST(SelectAgreement, BitSelectReachesTheSameBitInBothComponents) {
  ExpectSelectAgrees("[8:1]", "", "data[3]", 0xA5);
}

// The case fails when one component subtracts the low bound whatever the
// direction of the declaration.
// SelectAgreement.BitSelectReachesTheSameBitInBothComponents passes such a
// component, because its declaration descends. §11.5.1's own example is
// that `logic [15:0] acc;` and `logic [2:17] acc;` make one value of an index
// reach a different bit, and in `[1:8]` index 3 is storage offset 5. The driven
// word 8'h0C carries 0 at storage offset 5 and 1 at storage offsets 2 and 3.
TEST(SelectAgreement, AscendingDeclarationReachesTheSameBitInBothComponents) {
  ExpectSelectAgrees("[1:8]", "", "data[3]", 0x0C);
}

// The case fails when one component builds a bit-select and the other builds
// nothing for an indexed part-select, which the two cases above do not reach
// because each addresses one bit. It also fails when one component starts the
// run at index 2 and the other at storage offset 2: §11.5.1 rules that the
// `+:` form selects width_expr bits starting at the base and ascending the bit
// range, so `data[2 +: 4]` addresses indices 2 through 5, which are storage
// offsets 1 through 4 under `[8:1]`. The driven word 8'hA5 carries 4'h2 at
// storage offsets 1 through 4 and 4'h9 at storage offsets 2 through 5.
TEST(SelectAgreement, IndexedPartSelectPlusCoversTheSameBitsInBothComponents) {
  ExpectSelectAgrees("[8:1]", "[3:0]", "data[2 +: 4]", 0xA5);
}

// The case fails when one component gives `-:` the direction it gives `+:`,
// which SelectAgreement.IndexedPartSelectPlusCoversTheSameBitsInBothComponents
// passes because both components read that source in the same direction.
// §11.5.1 rules that the `-:` form starts at the base and descends the bit
// range, so `data[8 -: 4]` addresses indices 5 through 8 and not 8 through 11.
TEST(SelectAgreement, IndexedPartSelectMinusCoversTheSameBitsInBothComponents) {
  ExpectSelectAgrees("[8:1]", "[3:0]", "data[8 -: 4]", 0xA5);
}

// The case fails when one component counts the width of an indexed part-select
// from the low end of storage rather than along the declared range. The two
// cases above pass such a component, because their declarations descend and the
// two counts coincide there. §11.5.1 writes the indexed form against both
// directions at once: `b_vect[0 +: 8]` "== b_vect[0 : 7]" for `logic [0:31]
// b_vect`, so `data[2 +: 4]` under `[1:8]` addresses indices 2 through 5, which
// are storage offsets 6 down to 3.
TEST(SelectAgreement,
     AscendingIndexedPartSelectCoversTheSameBitsInBothComponents) {
  ExpectSelectAgrees("[1:8]", "[3:0]", "data[2 +: 4]", 0xA5);
}

// The case fails when the two components clip a part-select running past the
// top of the declared range to different runs of bits, which every case above
// leaves untested because each addresses bits the declaration holds. Indices 10
// and 9 are outside `[8:1]` and indices 8, 7 and 6 are inside it, so the two
// components have to agree on where the addressed run stops. The simulator
// answers x for a bit outside the declared range, and `Logic4Vec::ToUint64` in
// src/common/types.h projects x to 0, so the comparison is over which bits the
// components read and which they answer 0 for.
TEST(SelectAgreement,
     PartSelectRunningOffTheTopReadsTheSameBitsInBothComponents) {
  ExpectSelectAgrees("[8:1]", "[4:0]", "data[10:6]", 0xA5);
}

}  // namespace
