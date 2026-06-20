#include <cstdint>
#include <string>

#include "fixture_vcd.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.5 ("VCD SystemVerilog type mappings") states that SystemVerilog does
// not extend the IEEE Std 1364-2005 VCD format: a SystemVerilog data type is
// dumped by masquerading as a 1364-2005 type. Table 21-11 gives the mapping
// used to pick the var_type keyword and size written in each $var declaration.
// These tests drive the VcdWriter that emits the file (the output stage) and
// observe the declaration line produced for each data type.
//
// Two requirements of §21.7.5 are not exercised here because the simulator's
// runtime carries no information for the output stage to act on:
//   - A typed enum is dumped as its specified base type rather than the default
//     integer/32. Resolving an enum to its base type is an elaboration-time
//     decision; the writer faithfully dumps whichever resolved type it is
//     given, so the only enum-specific behavior at the output stage is the
//     default (kEnum -> integer/32), covered below. A typed enum is dumped
//     exactly like a plain variable of its base type, with no writer code
//     distinct from that base type's mapping.
//   - Unpacked arrays and automatic variables are not dumped. The writer is
//     handed one resolved object per $var with no tag marking it as an unpacked
//     array element or an automatic variable, so this omission rule cannot be
//     applied or observed at the output stage; it is left to whichever stage
//     selects the objects to register.
class VcdTypeMappingSim : public VcdTestBase {};

Variable* MakeVar(Arena& arena, uint32_t width) {
  auto* v = arena.Create<Variable>();
  v->value = MakeLogic4VecVal(arena, width, 0);
  return v;
}

// Table 21-11: bit and logic both masquerade as reg, dumped with the total size
// of the packed dimension. Registering a wide logic object also covers the rule
// that a packed array (or structure) is dumped as a single reg vector with its
// multiple packed dimensions collapsed into one dimension: a logic [3:0][7:0]
// object presents as a single 32-bit reg vector, never as nested ranges.
TEST_F(VcdTypeMappingSim, BitAndLogicDumpAsReg) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("flags", 4, MakeVar(arena_, 4), NetType::kWire, -1, -1,
                       VcdDataType::kBit);
    // logic [3:0][7:0] -> a single reg vector of the collapsed 32-bit width.
    vcd.RegisterSignal("word", 32, MakeVar(arena_, 32), NetType::kWire, -1, -1,
                       VcdDataType::kLogic);
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$var reg 4 ! flags $end"), std::string::npos);
  EXPECT_NE(content.find("$var reg 32 \" word $end"), std::string::npos);
  // A variable masquerades as reg, never as the net keyword wire (§21.7.2.3).
  EXPECT_EQ(content.find("$var wire"), std::string::npos);
}

// Table 21-11: the fixed-width integer types and the default enum each carry
// the keyword and size fixed by the table, independent of the object's stored
// width. int -> integer/32, shortint -> reg/16, longint -> reg/64, byte ->
// reg/8, and an untyped enum -> integer/32. Every object here is registered
// with a stored width that differs from its table size, so the size written in
// the declaration can only have come from the table lookup (VcdDataTypeSize)
// and not from echoing the registered width: if the writer echoed the width,
// none of these expectations would hold.
TEST_F(VcdTypeMappingSim, FixedWidthIntegerTypesUseTableSizes) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("myint", 8, MakeVar(arena_, 8), NetType::kWire, -1, -1,
                       VcdDataType::kInt);
    vcd.RegisterSignal("myshort", 8, MakeVar(arena_, 8), NetType::kWire, -1, -1,
                       VcdDataType::kShortint);
    vcd.RegisterSignal("mylong", 8, MakeVar(arena_, 8), NetType::kWire, -1, -1,
                       VcdDataType::kLongint);
    vcd.RegisterSignal("mybyte", 4, MakeVar(arena_, 4), NetType::kWire, -1, -1,
                       VcdDataType::kByte);
    vcd.RegisterSignal("myenum", 8, MakeVar(arena_, 8), NetType::kWire, -1, -1,
                       VcdDataType::kEnum);
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  // int: table size 32, not the 8-bit stored width.
  EXPECT_NE(content.find("$var integer 32 ! myint $end"), std::string::npos);
  // shortint: table size 16, not the 8-bit stored width.
  EXPECT_NE(content.find("$var reg 16 \" myshort $end"), std::string::npos);
  // longint: table size 64, not the 8-bit stored width.
  EXPECT_NE(content.find("$var reg 64 # mylong $end"), std::string::npos);
  // byte: table size 8, not the 4-bit stored width.
  EXPECT_NE(content.find("$var reg 8 $ mybyte $end"), std::string::npos);
  // The default (untyped) enum maps to integer with the table size 32, not its
  // 8-bit stored width.
  EXPECT_NE(content.find("$var integer 32 % myenum $end"), std::string::npos);
}

// Table 21-11: shortreal masquerades as the real type. The mapping is driven by
// the data type tag itself, so a kReal object is declared with the real keyword
// at the output stage, distinct from a 4-state object being detected as real by
// its stored value (§21.7.2.1).
TEST_F(VcdTypeMappingSim, ShortrealDumpsAsReal) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal("sr", 32, MakeVar(arena_, 32), NetType::kWire, -1, -1,
                       VcdDataType::kReal);
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$var real 32 ! sr $end"), std::string::npos);
  // It is not declared as a reg/integer integral type.
  EXPECT_EQ(content.find("$var reg"), std::string::npos);
  EXPECT_EQ(content.find("$var integer"), std::string::npos);
}

// §21.7.5: an unpacked structure appears as a named fork-join block so it is
// easy to distinguish from a begin-end block, and its member elements appear as
// their mapped types. The structure's scope therefore uses the fork keyword
// rather than module, with the members declared inside it under the type
// mapping.
TEST_F(VcdTypeMappingSim, UnpackedStructUsesForkScope) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.BeginScope("pkt", VcdScopeKind::kFork);
    vcd.RegisterSignal("header", 8, MakeVar(arena_, 8), NetType::kWire, -1, -1,
                       VcdDataType::kByte);
    vcd.RegisterSignal("valid", 1, MakeVar(arena_, 1), NetType::kWire, -1, -1,
                       VcdDataType::kBit);
    vcd.EndScope();
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$scope fork pkt $end"), std::string::npos);
  // The structure is not emitted as an ordinary module scope.
  EXPECT_EQ(content.find("$scope module pkt $end"), std::string::npos);
  // Its members appear under the scope as their mapped types.
  EXPECT_NE(content.find("$var reg 8 ! header $end"), std::string::npos);
  EXPECT_NE(content.find("$var reg 1 \" valid $end"), std::string::npos);
  EXPECT_NE(content.find("$upscope $end"), std::string::npos);
}

}  // namespace
}  // namespace delta
