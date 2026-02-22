// §21.7.2.1: Syntax of 4-state VCD file

#include <unistd.h>

#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>

#include "common/arena.h"
#include "gtest/gtest.h"
#include "simulation/variable.h"
#include "simulation/vcd_writer.h"

namespace delta {
namespace {

class VcdClause21070201Test : public ::testing::Test {
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

TEST_F(VcdClause21070201Test, WritesTimestamp) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.EndDefinitions();
    vcd.WriteTimestamp(42);
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("#42"), std::string::npos);
}

TEST_F(VcdClause21070201Test, IdentifierWrapsAround) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    for (int i = 0; i < 94; ++i) {
      auto *var = arena_.Create<Variable>();
      var->value = MakeLogic4VecVal(arena_, 1, 0);
      vcd.RegisterSignal("s", 1, var);
    }
    auto *var = arena_.Create<Variable>();
    var->value = MakeLogic4VecVal(arena_, 1, 0);
    vcd.RegisterSignal("wrap", 1, var);
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$var wire 1 ! wrap $end"), std::string::npos);
}

}  // namespace
}  // namespace delta
