#pragma once

#include <algorithm>
#include <filesystem>
#include <string>
#include <vector>

#include "fixture_scratch_dir.h"
#include "fixture_simulator.h"
#include "gtest/gtest.h"
#include "helpers_temp_file.h"
#include "simulator/vcd_writer.h"

class VcdDumpFromSourceTestBase : public ::testing::Test {
 protected:
  void RunSource(const std::string& src, bool close_file = true) {
    auto* design = ElaborateSrc(src, f_);
    ASSERT_NE(design, nullptr);
    LowerAndRun(design, f_);
    if (close_file) {
      f_.ctx.CloseVcdDump();
    } else {
      if (f_.ctx.Vcd().GetVcdWriter() != nullptr)
        f_.ctx.Vcd().GetVcdWriter()->Flush();
      if (f_.ctx.Vcd().GetDumpportsWriter() != nullptr) {
        f_.ctx.Vcd().GetDumpportsWriter()->Flush();
      }
    }
    ASSERT_FALSE(f_.diag.HasErrors());
  }

  std::string DumpFile(const std::string& name) const {
    auto path = scratch_.dir / name;
    if (!std::filesystem::exists(path)) return "<no-such-file>";
    return SlurpFile(path.string());
  }

  std::string NamesWritten() const {
    std::vector<std::string> names;
    for (const auto& entry :
         std::filesystem::directory_iterator(scratch_.dir)) {
      names.push_back(entry.path().filename().string());
    }
    std::sort(names.begin(), names.end());
    std::string joined;
    for (const auto& name : names) {
      if (!joined.empty()) joined += ' ';
      joined += name;
    }
    return joined;
  }

  ScratchWorkingDir scratch_;
  SimFixture f_;
};
