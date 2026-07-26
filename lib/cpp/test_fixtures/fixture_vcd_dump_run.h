#pragma once

#include <algorithm>
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

// A VcdTestBase that can drive a source through the whole pipeline the way the
// simulation driver does, for tests whose observable is the dump file a real
// run leaves on disk rather than anything hand-driven on the writer.
class VcdDumpRunTestBase : public VcdTestBase {
 protected:
  // Runs `src` through elaboration, lowering and the scheduler with the
  // driver's dump loop installed -- a timestamp and the changed values at the
  // end of each time unit -- and returns the contents of the dump file.
  //
  // Signals are registered in name order so identifier codes are
  // deterministic: the alphabetically first variable gets '!', the next '"',
  // and so on. A non-empty `scope` wraps the definitions in $scope/$upscope
  // the way the driver opens a module scope; an empty one leaves the
  // definitions at the top level. Value change dumping starts only once the
  // source's own $dumpvars or $dumpports executes.
  //
  // The fixture is caller-owned, so its diagnostics and context stay
  // inspectable after the run. Returns "<elaboration-failed>" when the source
  // does not elaborate.
  std::string RunVcdDump(SimFixture& f, const std::string& src,
                         std::string_view scope = {}) {
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    {
      VcdWriter vcd(tmp_path_);
      vcd.WriteHeader("1ns");
      if (!scope.empty()) vcd.BeginScope(scope);
      std::vector<std::pair<std::string_view, Variable*>> vars(
          f.ctx.GetVariables().begin(), f.ctx.GetVariables().end());
      std::sort(vars.begin(), vars.end(),
                [](const auto& a, const auto& b) { return a.first < b.first; });
      for (const auto& [name, var] : vars) {
        vcd.RegisterSignal(name, var->value.width, var);
      }
      if (!scope.empty()) vcd.EndScope();
      vcd.EndDefinitions();
      vcd.ArmDumpvarsStart();
      f.ctx.SetVcdWriter(&vcd);
      f.scheduler.SetPostTimestepCallback([&vcd, &f]() {
        vcd.WriteTimestamp(f.ctx.CurrentTime().ticks);
        vcd.DumpChangedValues(0);
      });
      f.scheduler.Run();
    }  // writer destructor flushes the dump to tmp_path_ before ReadVcd
    return ReadVcd();
  }

  // The same run for a test that has no interest in the fixture afterwards.
  std::string RunVcdDump(const std::string& src, std::string_view scope = {}) {
    SimFixture f;
    return RunVcdDump(f, src, scope);
  }
};
