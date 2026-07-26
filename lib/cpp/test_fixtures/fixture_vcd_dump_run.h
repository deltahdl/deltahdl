#pragma once

#include <algorithm>
#include <iostream>
#include <sstream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

// Completes the CoverageDB type that sim_context.h only forward-declares;
// included ahead of the fixtures so SimContext's inline constructor (whose
// unwind path destroys the owned coverage database) is well-formed in this TU.
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

using namespace delta;

// How a dump run produces its variable definitions.
enum class VcdSignalRegistration {
  // Registers every variable the context holds, in name order, so identifier
  // codes are deterministic: the alphabetically first variable gets '!', the
  // next '"', and so on. A test that wants a known, unfiltered signal set to
  // observe uses this.
  kAllVariablesSorted,
  // Defers to SimContext::RegisterVcdSignals, the registration the simulation
  // driver itself performs, which applies the §21.7.2.1 exclusions -- memories
  // are not dumped, an unpacked structure becomes a scope rather than one
  // object. A test whose subject is that filtering uses this.
  kContextFiltered,
};

// What one dump run varies. Each field is one of the steps the simulation
// driver takes around the run, so a test turns on exactly the steps the
// subclause it covers is about.
struct VcdDumpRunOptions {
  // Wraps the variable definitions in $scope/$upscope the way the driver opens
  // a module scope. Empty leaves the definitions at the top level.
  std::string_view scope = {};
  VcdSignalRegistration registration =
      VcdSignalRegistration::kAllVariablesSorted;
  // Marks the writer extended before the header, as a source's $dumpports
  // (§21.7.4) does: the definitions become port definitions and the value
  // changes carry port state rather than plain scalar values.
  bool extended = false;
  // Written as a $comment right after the definitions end, which is where the
  // driver may leave a note of its own.
  std::string_view driver_comment = {};
  // Runs the driver's close step -- the final simulation time reaching the
  // writer as the file is closed. Only a writer marked extended emits
  // anything there.
  bool close_file = false;
  // When set, stdout produced during the run is captured here rather than
  // reaching the terminal, so output a mid-simulation reader wrote can be
  // inspected after the run.
  std::string* captured_stdout = nullptr;
};

// A VcdTestBase that can drive a source through the whole pipeline the way the
// simulation driver does, for tests whose observable is the dump file a real
// run leaves on disk rather than anything hand-driven on the writer.
class VcdDumpRunTestBase : public VcdTestBase {
 protected:
  // Runs `src` through elaboration, lowering and the scheduler with the
  // driver's dump loop installed -- a timestamp and the changed values at the
  // end of each time unit -- and returns the contents of the dump file.
  //
  // Value change dumping starts only once the source's own $dumpvars or
  // $dumpports executes. The fixture is caller-owned, so its diagnostics and
  // context stay inspectable after the run. Returns "<elaboration-failed>"
  // when the source does not elaborate.
  std::string RunVcdDump(SimFixture& f, const std::string& src,
                         const VcdDumpRunOptions& opts = {}) {
    if (opts.captured_stdout != nullptr) opts.captured_stdout->clear();
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    std::ostringstream captured;
    {
      VcdWriter vcd(tmp_path_);
      if (opts.extended) {
        vcd.SetExtended();
        vcd.SetExtendedPortNodes();
      }
      vcd.WriteHeader("1ns");
      if (!opts.scope.empty()) vcd.BeginScope(opts.scope);
      RegisterSignals(f, vcd, opts.registration);
      if (!opts.scope.empty()) vcd.EndScope();
      vcd.EndDefinitions();
      if (!opts.driver_comment.empty()) vcd.WriteComment(opts.driver_comment);
      vcd.ArmDumpvarsStart();
      f.ctx.SetVcdWriter(&vcd);
      f.scheduler.SetPostTimestepCallback([&vcd, &f]() {
        vcd.WriteTimestamp(f.ctx.CurrentTime().ticks);
        vcd.DumpChangedValues(0);
      });
      std::streambuf* old_buf = nullptr;
      if (opts.captured_stdout != nullptr) {
        old_buf = std::cout.rdbuf(captured.rdbuf());
      }
      f.scheduler.Run();
      if (old_buf != nullptr) std::cout.rdbuf(old_buf);
      if (opts.close_file) vcd.WriteVcdClose(f.ctx.CurrentTime().ticks);
    }  // writer destructor flushes the dump to tmp_path_ before ReadVcd
    if (opts.captured_stdout != nullptr) *opts.captured_stdout = captured.str();
    return ReadVcd();
  }

  // The same run for a test with no interest in the fixture afterwards.
  std::string RunVcdDump(const std::string& src,
                         const VcdDumpRunOptions& opts = {}) {
    SimFixture f;
    return RunVcdDump(f, src, opts);
  }

 private:
  static void RegisterSignals(SimFixture& f, VcdWriter& vcd,
                              VcdSignalRegistration registration) {
    if (registration == VcdSignalRegistration::kContextFiltered) {
      f.ctx.RegisterVcdSignals(vcd);
      return;
    }
    std::vector<std::pair<std::string_view, Variable*>> vars(
        f.ctx.GetVariables().begin(), f.ctx.GetVariables().end());
    std::sort(vars.begin(), vars.end(),
              [](const auto& a, const auto& b) { return a.first < b.first; });
    for (const auto& [name, var] : vars) {
      vcd.RegisterSignal(name, var->value.width, var);
    }
  }
};

// A dump-run fixture for a test whose subject is what is on disk *during* the
// run rather than after it -- §21.7.1.6's $dumpflush and §21.7.3.5's
// $dumpportsflush, whose whole claim is that buffered records reach the file
// before the simulation ends. Procedural code in the design plays the reader:
// it opens the dump file mid-run, echoes the bytes it finds between marker
// lines, and closes it again, so the snapshot arrives on stdout where a run
// with `captured_stdout` set collects it.
class VcdMidRunReaderTestBase : public VcdDumpRunTestBase {
 protected:
  // SystemVerilog statements playing the reader: open the dump file, echo its
  // current contents to stdout delimited by <tag>-BEGIN/<tag>-END marker
  // lines, and close it. The enclosing module shall declare the integer
  // variables rfd and rch.
  std::string ReaderSnippet(const std::string& tag) const {
    return "$display(\"" + tag + "-BEGIN\");\n" +  //
           "rfd = $fopen(\"" + tmp_path_ + "\", \"r\");\n" +
           "rch = $fgetc(rfd);\n" + "while (rch != -1) begin\n" +
           "  $write(\"%c\", rch);\n" + "  rch = $fgetc(rfd);\n" + "end\n" +
           "$fclose(rfd);\n" + "$display(\"" + tag + "-END\");\n";
  }

  // The snapshot echoed between the tag's marker lines, or "<no-snapshot>"
  // when the run produced no such pair -- which a test reads as the reader
  // never having run.
  std::string MidDump(const std::string& tag) const {
    const std::string begin_marker = tag + "-BEGIN\n";
    auto b = run_output_.find(begin_marker);
    auto e = run_output_.find(tag + "-END");
    if (b == std::string::npos || e == std::string::npos) {
      return "<no-snapshot>";
    }
    b += begin_marker.size();
    return run_output_.substr(b, e - b);
  }

  // Everything the run wrote to stdout, which a RunVcdDump with
  // `captured_stdout` pointed here fills in.
  std::string run_output_;
};
