#pragma once

#include <algorithm>
#include <filesystem>
#include <string>
#include <vector>

// Completes the CoverageDB type that sim_context.h only forward-declares;
// included ahead of the fixtures so SimContext's inline constructor (whose
// unwind path destroys the owned coverage database) is well-formed in this TU.
#include "fixture_scratch_dir.h"
#include "fixture_simulator.h"
#include "gtest/gtest.h"
#include "helpers_temp_file.h"
#include "simulator/coverage.h"
#include "simulator/vcd_writer.h"

// A run whose dump file, if there is one, was created by the source and by
// nothing else.
//
// §21.7.1 lists two steps for creating a 4-state VCD file: insert the VCD
// system tasks in the SystemVerilog source file to define the dump file name
// and to specify the variables to be dumped, then run the simulation. A test
// of those two steps has to supply the source and nothing else, so this base
// drives a design through elaboration, lowering and the scheduler the way the
// simulation driver does and installs no VcdWriter of its own. That is what
// separates it from VcdDumpRunTestBase in fixture_vcd_dump_run.h, whose runs
// construct the writer, write the header and the variable definitions and
// install the per-timestep dump step before the source executes -- a run that
// has a dump file whatever the source's tasks do.
//
// The run stands in a scratch directory that is the process's working
// directory for the length of the test. The file names §21.7.1.1 deals in are
// relative: its default "dump.vcd" and its example "module1.dump" resolve
// against wherever the process stands, so a run left in the build tree would
// write over a concurrently running one and leave the file behind afterwards.
// The entry directory is restored and the scratch directory removed when the
// test ends.
class VcdDumpFromSourceTestBase : public ::testing::Test {
 protected:
  void SetUp() override {
    entry_dir_ = std::filesystem::current_path();
    std::filesystem::current_path(scratch_.dir);
  }

  void TearDown() override { std::filesystem::current_path(entry_dir_); }

  // Runs `src` the way the simulation driver runs a design -- elaboration,
  // lowering, then the scheduler -- supplying no VcdWriter, so whatever the
  // run leaves in the working directory the source's own tasks put there.
  //
  // `close_file` runs the driver's closing step, which RunSimulation in
  // src/main.cpp takes after the scheduler finishes: SimContext::CloseVcdDump
  // hands the writer the final simulation time and releases it, and the
  // release is what puts the dump on disk, since the writer holds a buffered
  // std::ofstream and a file small enough to sit entirely in that buffer reads
  // back empty until it is closed.
  //
  // A test whose subject is what the source's own tasks wrote turns that step
  // off, because it is the driver rather than the source that writes the
  // §21.7.3.6.1 close command there. The dump is flushed instead: §21.7.1.6
  // gives a flush no command of its own and leaves the dump state untouched,
  // so the file reads back holding exactly what the run put in it. A run whose
  // own tasks closed the dump has no writer left to flush, and neither has a
  // run that opened no dump at all.
  void RunSource(const std::string& src, bool close_file = true) {
    auto* design = ElaborateSrc(src, f_);
    ASSERT_NE(design, nullptr);
    LowerAndRun(design, f_);
    if (close_file) {
      f_.ctx.CloseVcdDump();
    } else if (f_.ctx.GetVcdWriter() != nullptr) {
      f_.ctx.GetVcdWriter()->Flush();
    }
    ASSERT_FALSE(f_.diag.HasErrors());
  }

  // The contents of `name` in the directory the run stood in, or
  // "<no-such-file>" when the run created no file of that name -- which a
  // test reads as the dump file never having been opened.
  std::string DumpFile(const std::string& name) const {
    auto path = scratch_.dir / name;
    if (!std::filesystem::exists(path)) return "<no-such-file>";
    return SlurpFile(path.string());
  }

  // Every name the run left in the directory it stood in, sorted and
  // space-separated, so a test claiming the run wrote nothing reports what it
  // wrote when the claim fails rather than a bare false.
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

  ScratchDir scratch_;
  SimFixture f_;
  std::filesystem::path entry_dir_;
};
