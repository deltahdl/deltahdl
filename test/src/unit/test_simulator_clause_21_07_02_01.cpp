#include <cstdint>
#include <cstring>

#include "fixture_vcd.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

class VcdFileSyntaxSim : public VcdTestBase {};

// Build a real-valued Logic4Vec holding the IEEE Std 754 bit pattern of d,
// mirroring how the evaluator stores real results.
Logic4Vec MakeReal(Arena& arena, double d) {
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  Logic4Vec v = MakeLogic4VecVal(arena, 64, bits);
  v.is_real = true;
  return v;
}

// Build a 1-bit Logic4Vec from raw aval/bval bits so all four logic states can
// be exercised: (0,0)=0, (1,0)=1, (0,1)=x, (1,1)=z.
Logic4Vec MakeScalar(Arena& arena, uint64_t aval, uint64_t bval) {
  Logic4Vec v = MakeLogic4VecVal(arena, 1, aval);
  v.words[0].bval = bval;
  return v;
}

TEST_F(VcdFileSyntaxSim, IdentifierWrapsAround) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    for (int i = 0; i < 94; ++i) {
      auto* var = arena_.Create<Variable>();
      var->value = MakeLogic4VecVal(arena_, 1, 0);
      vcd.RegisterSignal("s", 1, var);
    }
    auto* var = arena_.Create<Variable>();
    var->value = MakeLogic4VecVal(arena_, 1, 0);
    vcd.RegisterSignal("wrap", 1, var);
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$var wire 1 ! wrap $end"), std::string::npos);
}

// Syntax 21-20: a 4-state VCD file opens with a sequence of declaration
// commands. Verify the header section produces $date, $version, $timescale,
// $scope/$upscope, and $enddefinitions, and that $enddefinitions terminates the
// declarations after the variable definitions.
TEST_F(VcdFileSyntaxSim, DeclarationCommandsFormHeader) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.BeginScope("top");
    auto* var = arena_.Create<Variable>();
    var->value = MakeLogic4VecVal(arena_, 1, 0);
    vcd.RegisterSignal("clk", 1, var);
    vcd.EndScope();
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$date"), std::string::npos);
  EXPECT_NE(content.find("$version"), std::string::npos);
  EXPECT_NE(content.find("$timescale\n  1ns\n$end"), std::string::npos);
  EXPECT_NE(content.find("$scope module top $end"), std::string::npos);
  EXPECT_NE(content.find("$upscope $end"), std::string::npos);

  auto var_pos = content.find("$var wire 1 ! clk $end");
  auto end_defs = content.find("$enddefinitions $end");
  EXPECT_NE(var_pos, std::string::npos);
  EXPECT_NE(end_defs, std::string::npos);
  EXPECT_LT(var_pos, end_defs);
}

// §21.7.2.1: value changes for real variables are specified by real numbers,
// emitted as the r-form vector_value_change rather than a binary b-form.
TEST_F(VcdFileSyntaxSim, RealVariableDumpedAsRealNumber) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto* var = arena_.Create<Variable>();
    var->value = MakeReal(arena_, 2.5);
    vcd.RegisterSignal("r", 64, var);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  // The change is the r-form with the value adjacent to the base letter and a
  // single space before the identifier code.
  EXPECT_NE(content.find("r2.5 !"), std::string::npos);
  // It must not be emitted as a binary vector (b<bits>) for this signal.
  EXPECT_EQ(content.find("b0"), std::string::npos);
  EXPECT_EQ(content.find("b1"), std::string::npos);
}

// §21.7.2.1: a real number is dumped using a %.16g format, preserving all 53
// mantissa bits. A %g-only formatter would truncate 1/3 to "0.333333".
TEST_F(VcdFileSyntaxSim, RealNumberUsesFullPrecision) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto* var = arena_.Create<Variable>();
    var->value = MakeReal(arena_, 1.0 / 3.0);
    vcd.RegisterSignal("r", 64, var);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("r0.3333333333333333 !"), std::string::npos);
}

// §21.7.2.1 (var_type production): a real variable is declared with the real
// var_type keyword, distinguishing it from a binary-valued wire.
TEST_F(VcdFileSyntaxSim, RealVariableDeclaredWithRealVarType) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto* var = arena_.Create<Variable>();
    var->value = MakeReal(arena_, 0.0);
    vcd.RegisterSignal("freq", 64, var);
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$var real 64 ! freq $end"), std::string::npos);
}

// §21.7.2.1: value changes for non-real variables are given in binary form as
// one of 0, 1, x, or z. Exercise all four logic states, including the unknown
// (x) and high-impedance (z) edge cases, and confirm each maps to its value
// character against the registration-ordered identifier codes.
TEST_F(VcdFileSyntaxSim, ScalarFourStateValuesUseBinaryCharacters) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto* zero = arena_.Create<Variable>();
    zero->value = MakeScalar(arena_, 0, 0);
    vcd.RegisterSignal("z0", 1, zero);  // ident '!'
    auto* one = arena_.Create<Variable>();
    one->value = MakeScalar(arena_, 1, 0);
    vcd.RegisterSignal("o1", 1, one);  // ident '"'
    auto* unknown = arena_.Create<Variable>();
    unknown->value = MakeScalar(arena_, 0, 1);
    vcd.RegisterSignal("ux", 1, unknown);  // ident '#'
    auto* highz = arena_.Create<Variable>();
    highz->value = MakeScalar(arena_, 1, 1);
    vcd.RegisterSignal("hz", 1, highz);  // ident '$'
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("0!"), std::string::npos);
  EXPECT_NE(content.find("1\""), std::string::npos);
  EXPECT_NE(content.find("x#"), std::string::npos);
  EXPECT_NE(content.find("z$"), std::string::npos);
}

// §21.7.2.1: the time recorded by a simulation_time command is the absolute
// simulation time, not an increment relative to the previous timestamp. Two
// successive timestamps must both appear with their absolute values, and the
// delta between them must not.
TEST_F(VcdFileSyntaxSim, SimulationTimesAreAbsolute) {
  {
    VcdWriter vcd(tmp_path_);
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

}  // namespace
}  // namespace delta
