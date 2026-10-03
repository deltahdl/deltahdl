#pragma once

#include <stdlib.h>
#include <unistd.h>

#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>

#include "common/arena.h"
#include "fixture_scratch_dir.h"
#include "gtest/gtest.h"

using namespace delta;

// The dump a test's writer produces goes to `tmp_path_`, and a dump file the
// test's source names relatively (§21.7.1.1) to the scratch directory the test
// stands in for its length, removed when it ends.
class VcdTestBase : public ::testing::Test {
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

  ScratchWorkingDir working_dir_;
  std::string tmp_path_;
  Arena arena_;
};
