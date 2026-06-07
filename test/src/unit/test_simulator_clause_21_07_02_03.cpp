#include "fixture_vcd.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

class VcdHeaderAndScopeSim : public VcdTestBase {};

TEST_F(VcdHeaderAndScopeSim, WritesHeader) {
  {
    VcdWriter vcd(tmp_path_);
    ASSERT_TRUE(vcd.IsOpen());
    vcd.WriteHeader("1ns");
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$date"), std::string::npos);
  EXPECT_NE(content.find("DeltaHDL"), std::string::npos);
  EXPECT_NE(content.find("1ns"), std::string::npos);
  EXPECT_NE(content.find("$enddefinitions"), std::string::npos);
}

TEST_F(VcdHeaderAndScopeSim, WritesScope) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.BeginScope("top");
    vcd.EndScope();
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$scope module top $end"), std::string::npos);
  EXPECT_NE(content.find("$upscope $end"), std::string::npos);
}

TEST_F(VcdHeaderAndScopeSim, RegistersSignal) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto* var = arena_.Create<Variable>();
    var->value = MakeLogic4VecVal(arena_, 1, 0);
    vcd.RegisterSignal("clk", 1, var);
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$var wire 1"), std::string::npos);
  EXPECT_NE(content.find("clk"), std::string::npos);
}

// §21.7.2.3: in the $var section a net of net type uwire shall have a var_type
// of wire. The writer recognizes the uwire net type and records it as wire.
TEST_F(VcdHeaderAndScopeSim, UwireNetIsRecordedAsWire) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto* var = arena_.Create<Variable>();
    var->value = MakeLogic4VecVal(arena_, 1, 0);
    vcd.RegisterSignal("uw", 1, var, NetType::kUwire);
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$var wire 1"), std::string::npos);
  // The uwire keyword itself never appears as a var_type.
  EXPECT_EQ(content.find("uwire"), std::string::npos);
}

// §21.7.2.3: if a filename literal was used in $dumpfile, that literal shall
// appear in the $version section. A string-literal filename is reproduced
// inside a $dumpfile(...) entry of $version.
TEST_F(VcdHeaderAndScopeSim, VersionContainsDumpfileLiteral) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns", "\"dump1.dump\"");
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  auto version_pos = content.find("$version");
  ASSERT_NE(version_pos, std::string::npos);
  auto dumpfile_pos = content.find("$dumpfile(\"dump1.dump\")");
  ASSERT_NE(dumpfile_pos, std::string::npos);
  // The $dumpfile literal lives within the $version section, before its $end.
  EXPECT_LT(version_pos, dumpfile_pos);
  EXPECT_LT(dumpfile_pos, content.find("$end", version_pos));
}

// §21.7.2.3: the $dumpfile entry is reproduced in $version only when a filename
// literal was supplied. When none is given, the gating condition is false and
// $version carries no $dumpfile entry.
TEST_F(VcdHeaderAndScopeSim, VersionOmitsDumpfileWithoutLiteral) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$version"), std::string::npos);
  EXPECT_EQ(content.find("$dumpfile("), std::string::npos);
}

}
}
