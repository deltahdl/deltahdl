// §21.7.1.2: $dumpvars

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

class VcdClause21070102Test : public ::testing::Test {
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

TEST_F(VcdClause21070102Test, ScalarValueChange) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto *var = arena_.Create<Variable>();
    var->value = MakeLogic4VecVal(arena_, 1, 1);
    vcd.RegisterSignal("clk", 1, var);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$dumpvars"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

TEST_F(VcdClause21070102Test, VectorValueChange) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto *var = arena_.Create<Variable>();
    var->value = MakeLogic4VecVal(arena_, 8, 0xA5);
    vcd.RegisterSignal("data", 8, var);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("b10100101 !"), std::string::npos);
}

} // namespace
} // namespace delta
