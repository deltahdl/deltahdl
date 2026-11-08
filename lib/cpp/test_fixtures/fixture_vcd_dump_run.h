#pragma once

#include <algorithm>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

using namespace delta;

enum class VcdSignalRegistration : uint8_t {
  kAllVariablesSorted,
  kContextFiltered,
};

struct VcdDumpRunOptions {
  std::string_view scope = {};
  VcdSignalRegistration registration =
      VcdSignalRegistration::kAllVariablesSorted;
  bool extended = false;
  std::string_view driver_comment = {};
  bool close_file = false;
  std::string* captured_stdout = nullptr;
};

class VcdDumpRunTestBase : public VcdTestBase {
 protected:
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
      vcd.SetTopScope(opts.scope);
      if (!opts.scope.empty()) vcd.BeginScope(opts.scope);
      RegisterSignals(f, vcd, opts.registration);
      if (!opts.scope.empty()) vcd.EndScope();
      if (opts.registration == VcdSignalRegistration::kContextFiltered)
        f.ctx.RegisterVcdPackageSignals(vcd);
      vcd.EndDefinitions();
      if (!opts.driver_comment.empty()) vcd.WriteComment(opts.driver_comment);
      vcd.ArmDumpvarsStart();
      f.ctx.Vcd().SetVcdWriter(&vcd);
      f.scheduler.AddPostTimestepCallback([&vcd, &f]() {
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
    }
    if (opts.captured_stdout != nullptr) *opts.captured_stdout = captured.str();
    return ReadVcd();
  }

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
      vcd.RegisterSignal(VcdSignalSpec{.name = name,
                                       .width = var->value.width,
                                       .var = var,
                                       .data_type = VcdDataTypeForDeclKind(
                                           f.ctx.Vcd().GetVcdVarKind(name))});
    }
  }
};

class VcdMidRunReaderTestBase : public VcdDumpRunTestBase {
 protected:
  std::string ReaderSnippet(const std::string& tag) const {
    return "$display(\"" + tag + "-BEGIN\");\n" + "rfd = $fopen(\"" +
           tmp_path_ + "\", \"r\");\n" + "rch = $fgetc(rfd);\n" +
           "while (rch != -1) begin\n" + "  $write(\"%c\", rch);\n" +
           "  rch = $fgetc(rfd);\n" + "end\n" + "$fclose(rfd);\n" +
           "$display(\"" + tag + "-END\");\n";
  }

  std::string MidDump(const std::string& tag) const {
    const std::string kBeginMarker = tag + "-BEGIN\n";
    auto b = run_output_.find(kBeginMarker);
    auto e = run_output_.find(tag + "-END");
    if (b == std::string::npos || e == std::string::npos) {
      return "<no-snapshot>";
    }
    b += kBeginMarker.size();
    return run_output_.substr(b, e - b);
  }

  std::string run_output_;
};
