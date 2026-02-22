// §21.7.1.3: $dumpoff / $dumpon

#include <unistd.h>

#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>

#include "common/arena.h"
#include "gtest/gtest.h"
#include "simulation/vcd_writer.h"

namespace delta {
namespace {

class VcdClause21070103Test : public ::testing::Test {
 protected:
  void SetUp() override {
    char tmpl[] = "/tmp/test_vcd_XXXXXX";
    int fd = mkstemp(tmpl);
    close(fd);
    tmp_path_ = tmpl;
  }

  void TearDown() override { std::remove(tmp_path_.c_str()); }

  std::string ReadVcd() {
    std::ifstream ifs(tmp_path_);
    std::ostringstream ss;
    ss << ifs.rdbuf();
    return ss.str();
  }

  std::string tmp_path_;
  Arena arena_;
};

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
