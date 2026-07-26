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

// What one dump run varies.
struct VcdDumpRunOptions {
  // Wraps the variable definitions in $scope/$upscope the way the driver opens
  // a module scope. Empty leaves the definitions at the top level.
  std::string_view scope = {};
  VcdSignalRegistration registration =
      VcdSignalRegistration::kAllVariablesSorted;
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
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    std::ostringstream captured;
    {
      VcdWriter vcd(tmp_path_);
      vcd.WriteHeader("1ns");
      if (!opts.scope.empty()) vcd.BeginScope(opts.scope);
      RegisterSignals(f, vcd, opts.registration);
      if (!opts.scope.empty()) vcd.EndScope();
      vcd.EndDefinitions();
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
