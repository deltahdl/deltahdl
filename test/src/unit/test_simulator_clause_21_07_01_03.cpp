// §21.7.1.3: $dumpoff / $dumpon

#include "simulator/vcd_writer.h"
#include "fixture_vcd.h"

namespace delta {
namespace {

class VcdClause21070103Test : public VcdTestBase {};

TEST_F(VcdClause21070103Test, DisabledWriterSkipsOutput) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.EndDefinitions();
    vcd.SetEnabled(false);
    EXPECT_FALSE(vcd.IsEnabled());
    vcd.WriteTimestamp(100);
  }
  auto content = ReadVcd();
  EXPECT_EQ(content.find("#100"), std::string::npos);
}

TEST_F(VcdClause21070103Test, ReEnableAfterDisable) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.EndDefinitions();
    vcd.SetEnabled(false);
    vcd.WriteTimestamp(100);
    vcd.SetEnabled(true);
    vcd.WriteTimestamp(200);
  }
  auto content = ReadVcd();
  EXPECT_EQ(content.find("#100"), std::string::npos);
  EXPECT_NE(content.find("#200"), std::string::npos);
}

}  // namespace
}  // namespace delta
