#include <cstdint>
#include <cstring>

#include "fixture_vcd.h"
#include "helpers_vcd_four_state_scalars.h"
#include "helpers_vcd_logic4vec.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.4.1 (Syntax 21-27) defines the output format of the extended VCD file.
// The format is realized by the same VcdWriter that produces the 4-state file:
// per the clause's opening rule, a 4-state construct name that matches an
// extended construct is equivalent, so the extended writer reuses the inherited
// declaration and value-change machinery and adds only the extended-only
// $vcdclose keyword command. These tests observe that reuse and the format
// properties §21.7.4.1 states directly.
class ExtendedVcdSyntaxSim : public VcdTestBase {};

// Build a width-bit Logic4Vec from a raw value, mirroring how the evaluator
// stores a port's resolved value.
Logic4Vec MakeBits(Arena& arena, uint32_t width, uint64_t val) {
  return MakeLogic4VecVal(arena, width, val);
}

// §21.7.4.1: "A 4-state VCD construct name that matches an extended VCD
// construct shall be considered equivalent ...". An extended writer therefore
// emits the same declaration construct names ($date, $version, $timescale,
// $scope/$upscope, $var, $enddefinitions) as a 4-state writer, while the
// extended-only $vcdclose keyword command confirms the file is the extended
// form rather than the 4-state form.
TEST_F(ExtendedVcdSyntaxSim, ExtendedFileReusesFourStateConstructNames) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.WriteHeader("1ns");
    vcd.BeginScope("top");
    auto* var = arena_.Create<Variable>();
    var->value = MakeBits(arena_, 1, 1);
    vcd.RegisterSignal("clk", 1, var);
    vcd.EndScope();
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
    vcd.WriteVcdClose(500);
  }
  auto content = ReadVcd();
  // The 4-state declaration construct names carry over unchanged.
  EXPECT_NE(content.find("$date"), std::string::npos);
  EXPECT_NE(content.find("$version"), std::string::npos);
  EXPECT_NE(content.find("$timescale\n  1ns\n$end"), std::string::npos);
  EXPECT_NE(content.find("$scope module top $end"), std::string::npos);
  EXPECT_NE(content.find("$var wire 1 ! clk $end"), std::string::npos);
  EXPECT_NE(content.find("$upscope $end"), std::string::npos);
  EXPECT_NE(content.find("$enddefinitions $end"), std::string::npos);
  // The extended-only keyword command is what distinguishes this from a 4-state
  // file, so the equivalence above is being observed on a genuine extended
  // file.
  EXPECT_NE(content.find("$vcdclose #500 $end"), std::string::npos);
}

// §21.7.4.1: "Data in the extended VCD file are case sensitive." The writer
// records scope and reference names verbatim, so a mixed-case name is preserved
// exactly and is not folded to another case.
TEST_F(ExtendedVcdSyntaxSim, ExtendedDataAreCaseSensitive) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.WriteHeader("1ns");
    vcd.BeginScope("TopMod");
    auto* var = arena_.Create<Variable>();
    var->value = MakeBits(arena_, 1, 0);
    vcd.RegisterSignal("MixedCaseNet", 1, var);
    vcd.EndScope();
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  // The names appear with their original case ...
  EXPECT_NE(content.find("$scope module TopMod $end"), std::string::npos);
  EXPECT_NE(content.find("MixedCaseNet"), std::string::npos);
  // ... and are not case-folded.
  EXPECT_EQ(content.find("topmod"), std::string::npos);
  EXPECT_EQ(content.find("mixedcasenet"), std::string::npos);
}

// §21.7.4.1: the extended VCD format provides no mechanism to dump part of a
// vector; the entire vector is dumped instead. A multi-bit port therefore emits
// one full-width value change carrying every bit, never a sub-range selection.
TEST_F(ExtendedVcdSyntaxSim, ExtendedDumpsWholeVectorNotPartialSelection) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.WriteHeader("1ns");
    auto* var = arena_.Create<Variable>();
    var->value = MakeBits(arena_, 8, 0xA5);  // 1010_0101, MSB set
    vcd.RegisterSignal("bus", 8, var);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  // Every one of the eight bits is present in a single value change; the most
  // significant bit is set, so no bit is dropped by leading-digit shortening.
  EXPECT_NE(content.find("b10100101 !"), std::string::npos);
  // No partial-selection syntax (e.g. a [8:15] sub-range) is ever emitted.
  EXPECT_EQ(content.find('['), std::string::npos);
}

// §21.7.4.1: port value changes are given in binary form as one of 0, 1, x, or
// z. Exercise all four logic states on an extended writer, including the
// unknown (x) and high-impedance (z) edge cases, confirming each maps to its
// value character against the registration-ordered identifier codes. (The
// clause also states a value carries strength information; the writer does not
// model port strength, so only the binary-character rule is observed here.)
TEST_F(ExtendedVcdSyntaxSim, ExtendedScalarPortValuesUseBinaryCharacters) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    WriteFourStateScalarDump(vcd, arena_);
  }
  ExpectFourStateScalarChars(ReadVcd());
}

// §21.7.4.1: within a time increment, only the ports whose value changed are
// listed. With one port changed since the previous step and one unchanged, the
// extended writer records only the changed port's value change.
TEST_F(ExtendedVcdSyntaxSim, ExtendedOnlyListsPortsThatChanged) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.WriteHeader("1ns");
    auto* changed = arena_.Create<Variable>();
    changed->value = MakeBits(arena_, 8, 0x3C);
    changed->prev_value = MakeBits(arena_, 8, 0x00);  // differs -> changed
    vcd.RegisterSignal("moved", 8, changed);          // ident '!'
    auto* steady = arena_.Create<Variable>();
    steady->value = MakeBits(arena_, 8, 0xA5);
    steady->prev_value = MakeBits(arena_, 8, 0xA5);  // equal -> unchanged
    vcd.RegisterSignal("still", 8, steady);          // ident '"'
    vcd.EndDefinitions();
    vcd.WriteTimestamp(100);
    vcd.DumpChangedValues(0);
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("b111100 !"), std::string::npos);  // moved listed
  // The steady port emits no value change (its bit pattern never appears as a
  // value; its identifier still appears only in the $var declaration).
  EXPECT_EQ(content.find("b10100101"), std::string::npos);
}

// §21.7.4.1: the time recorded by a simulation_time command is the absolute
// simulation time of the value changes that follow, not an increment from the
// previous timestamp. Both absolute times appear; their delta does not.
TEST_F(ExtendedVcdSyntaxSim, ExtendedSimulationTimesAreAbsolute) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.WriteHeader("1ns");
    vcd.EndDefinitions();
    vcd.WriteTimestamp(100);
    vcd.WriteTimestamp(250);
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("#100"), std::string::npos);
  EXPECT_NE(content.find("#250"), std::string::npos);
  EXPECT_EQ(content.find("#150"), std::string::npos);
}

// §21.7.4.1: a real number is dumped with a %.16g format so all 53 mantissa
// bits survive. A %g-only formatter would truncate 1/3 to "0.333333".
TEST_F(ExtendedVcdSyntaxSim, ExtendedRealUsesFullPrecision) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.SetExtended();
    vcd.WriteHeader("1ns");
    auto* var = arena_.Create<Variable>();
    var->value = MakeReal(arena_, 1.0 / 3.0);
    vcd.RegisterSignal("freq", 64, var);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("r0.3333333333333333 !"), std::string::npos);
}

}  // namespace
}  // namespace delta
