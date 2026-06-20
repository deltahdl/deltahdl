#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// Exercises the $vcdclose keyword command (§21.7.3.6.1) as the production
// VcdWriter emits it when an extended VCD file is closed.
class VcdcloseKeyword : public VcdTestBase {};

// §21.7.3.6.1 / Syntax 21-26: an extended VCD file is closed with
// "$vcdclose <final_simulation_time> $end". The keyword records the end
// simulation time at the moment of close regardless of signal activity, so the
// recorded time is the final simulation time passed at close — here #13000 —
// even though the last value change happened earlier at #500. This one positive
// case observes both the keyword format and the "regardless of the state of
// signal changes" semantics through the single emit branch.
TEST_F(VcdcloseKeyword, ExtendedVcdRecordsFinalSimulationTime) {
  SimFixture f;
  auto* data = MakeVar(f, "data", 8, 0xA5);
  VcdWriter vcd(tmp_path_);
  vcd.SetExtended();
  vcd.WriteHeader("1ns");
  vcd.RegisterSignal("data", 8, data);
  vcd.EndDefinitions();
  vcd.WriteTimestamp(500);
  vcd.DumpAllValues();

  vcd.WriteVcdClose(13000);

  auto content = ReadVcd();
  EXPECT_NE(content.find("$vcdclose #13000 $end"), std::string::npos);
  // The close time is the final simulation time, not the last value-change
  // time.
  EXPECT_EQ(content.find("$vcdclose #500"), std::string::npos);
}

// §21.7.3.6.1 in context of §21.7.3.6: $vcdclose is the one keyword command the
// extended VCD format adds over the 4-state format. A writer that was never
// marked extended emits no $vcdclose at close, so a 4-state VCD file is left
// unchanged. This observes the extended-only gating branch.
TEST_F(VcdcloseKeyword, FourStateVcdOmitsVcdclose) {
  SimFixture f;
  auto* data = MakeVar(f, "data", 8, 0xA5);
  VcdWriter vcd(tmp_path_);
  vcd.WriteHeader("1ns");
  vcd.RegisterSignal("data", 8, data);
  vcd.EndDefinitions();
  vcd.WriteTimestamp(0);
  vcd.DumpAllValues();

  vcd.WriteVcdClose(13000);

  EXPECT_EQ(ReadVcd().find("$vcdclose"), std::string::npos);
}

// §21.7.3.6.1 edge: closing the dump is harmless when no dump file was ever
// opened. WriteVcdClose guards on an open output stream, so an extended writer
// whose file failed to open writes nothing and does not fault. The path uses a
// destination under an existing regular file so the stream cannot open.
TEST_F(VcdcloseKeyword, WithoutOpenFileIsHarmless) {
  VcdWriter vcd(tmp_path_ + "/cannot_open.vcd");
  ASSERT_FALSE(vcd.IsOpen());
  vcd.SetExtended();
  vcd.WriteVcdClose(13000);
  EXPECT_FALSE(vcd.IsOpen());
}

}  // namespace
}  // namespace delta
