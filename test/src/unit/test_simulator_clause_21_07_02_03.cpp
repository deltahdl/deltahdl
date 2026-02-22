// §21.7.2.3: Description of keyword commands

#include <unistd.h>

#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>

#include "common/arena.h"
#include "simulation/variable.h"
#include "simulation/vcd_writer.h"
#include "gtest/gtest.h"

namespace delta {
namespace {

class VcdClause21070203Test : public ::testing::Test {
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

TEST_F(VcdClause21070203Test, WritesHeader) {
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

TEST_F(VcdClause21070203Test, WritesScope) {
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

TEST_F(VcdClause21070203Test, RegistersSignal) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto *var = arena_.Create<Variable>();
    var->value = MakeLogic4VecVal(arena_, 1, 0);
    vcd.RegisterSignal("clk", 1, var);
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$var wire 1"), std::string::npos);
  EXPECT_NE(content.find("clk"), std::string::npos);
}

} // namespace
} // namespace delta
