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

class VcdWriterTest : public ::testing::Test {
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

TEST_F(VcdWriterTest, WritesHeader) {
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

TEST_F(VcdWriterTest, WritesScope) {
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

TEST_F(VcdWriterTest, RegistersSignal) {
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

TEST_F(VcdWriterTest, WritesTimestamp) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.EndDefinitions();
    vcd.WriteTimestamp(42);
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("#42"), std::string::npos);
}

TEST_F(VcdWriterTest, ScalarValueChange) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto* var = arena_.Create<Variable>();
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

TEST_F(VcdWriterTest, VectorValueChange) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto* var = arena_.Create<Variable>();
    var->value = MakeLogic4VecVal(arena_, 8, 0xA5);
    vcd.RegisterSignal("data", 8, var);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("b10100101 !"), std::string::npos);
}

TEST_F(VcdWriterTest, DumpChangedValuesOnlyEmitsChanged) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto* var_a = arena_.Create<Variable>();
    var_a->value = MakeLogic4VecVal(arena_, 1, 0);
    var_a->prev_value = MakeLogic4VecVal(arena_, 1, 0);
    auto* var_b = arena_.Create<Variable>();
    var_b->value = MakeLogic4VecVal(arena_, 1, 1);
    var_b->prev_value = MakeLogic4VecVal(arena_, 1, 0);
    vcd.RegisterSignal("a", 1, var_a);
    vcd.RegisterSignal("b", 1, var_b);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(10);
    vcd.DumpChangedValues(0);
  }
  auto content = ReadVcd();
  // 'b' changed (0->1), identifier is '"' (second signal: '!' + 1).
  EXPECT_NE(content.find("1\""), std::string::npos);
}

TEST_F(VcdWriterTest, DisabledWriterSkipsOutput) {
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

TEST_F(VcdWriterTest, ReEnableAfterDisable) {
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

TEST_F(VcdWriterTest, FourValueScalar) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto* var = arena_.Create<Variable>();
    var->value = MakeLogic4Vec(arena_, 1);
    var->value.words[0].aval = 0;
    var->value.words[0].bval = 1;
    vcd.RegisterSignal("sig", 1, var);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("x!"), std::string::npos);
}

TEST_F(VcdWriterTest, IdentifierWrapsAround) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    // Register 94 signals ('!' to '~'), then one more wraps to '!'.
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

}  // namespace
}  // namespace delta
