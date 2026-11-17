#pragma once

#include <cstddef>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>

#include "common/diagnostic.h"
#include "fixture_simulator.h"

using namespace delta;

struct ControlRun {
  std::string out;
  std::string err;
  uint32_t warnings = 0;
  int fails = 0;
  uint64_t cover_succeeded = 0;
  uint64_t cover_evaluated = 0;
  std::string warning_lines;
};

inline ControlRun RunControlled(const std::string& src) {
  std::ostringstream err;
  std::streambuf* old = std::cerr.rdbuf(err.rdbuf());
  SimFixture f;
  ControlRun run;
  run.out = RunCapture(src, f);
  std::cerr.rdbuf(old);
  run.err = err.str();
  run.warnings = f.diag.WarningCount();
  run.fails = f.ctx.AssertionFailCount();
  run.cover_succeeded = f.ctx.ImmediateCovers().Succeeded();
  run.cover_evaluated = f.ctx.ImmediateCovers().Evaluated();
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.severity != DiagSeverity::kWarning) continue;
    if (!run.warning_lines.empty()) run.warning_lines += ' ';
    run.warning_lines += std::to_string(d.loc.line);
  }
  for (const auto& r : f.ctx.ConcurrentCovers().Results()) {
    run.cover_succeeded += r.succeeded;
  }
  return run;
}

inline std::string ErrorTimes(const std::string& err) {
  std::string times;
  size_t pos = 0;
  while ((pos = err.find("] ERROR ", pos)) != std::string::npos) {
    size_t open = err.rfind('[', pos);
    if (!times.empty()) times += ' ';
    times += err.substr(open + 1, pos - open - 1);
    pos += 8;
  }
  return times;
}

inline std::string ControlledErrorTimes(const std::string& src) {
  return ErrorTimes(RunControlled(src).err);
}

inline std::string ControlledOutput(const std::string& src) {
  return RunControlled(src).out;
}
