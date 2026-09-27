#pragma once

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

// The design, the readbacks and the SDF wrappers
// test_simulator_subclause_32_04_01a.cpp's §32.4.1 and §32.4.2 mapping cases
// share, split out of that file.

// §32.4.1 says which SystemVerilog *declaration* each SDF delay construct lands
// on, so which declarations exist -- and how each one was written -- is the
// whole subject. Every test below therefore builds its SystemVerilog side from
// real source: BuildSpecifyFromSource parses, elaborates and runs a module and
// then fills a SpecifyManager from that module using only production builders.
// Module path assignments come in through §30.4.2/§30.4.4/§30.4.4.4 syntax and
// BuildPathDelayFromDecl, PATHPULSE$ pulse limits through §30.7.1's resolver,
// timing checks through §31.2/§31.7 declarations, and the primitives that drive
// module outputs through gate instantiations. Nothing here is hand-assembled.
inline bool BuildSpecifyFromSource(const std::string& src, SimFixture& f,
                                   SpecifyManager& mgr) {
  auto* cu = RunModuleSource(src, f);
  if (cu == nullptr) return false;
  const ModuleDecl& mod = *cu->modules.back();
  RegisterPrimitiveDrivers(mod, f, mgr);
  RegisterPathDelays(mod, f, mgr, /*default_pulse_limits=*/true);
  RegisterTimingChecks(mod, f, mgr);
  RegisterPathPulseSpecparams(mod, f, mgr);
  return true;
}

// The design most tests annotate onto. Between a and y it declares the three
// forms a module path can take that differ only by condition -- two
// state-dependent paths (§30.4.4/§30.4.4.1) and the ifnone path that covers the
// rest (§30.4.4.4) -- so a construct that is supposed to reach one of them can
// be checked against the two it must leave alone. The b to z path (§30.4.2) is
// the unconditional endpoint pair no a-to-y construct may touch. Every declared
// value is distinct, so untouched never reads as overwritten. The two $setup
// checks differ only by condition and the $hold only by type, which is what
// makes the timing check matching rule observable. $setup writes its data event
// first (Syntax 31-3) and $hold its reference event first (Syntax 31-4), so the
// three timing check declarations below name d as the data signal and clk as
// the reference one despite writing their arguments in opposite orders.
inline const char* const kDesign =
    "module t(input a, input b, input mode, input clk, input d,\n"
    "         output y, output z);\n"
    "  reg ntf;\n"
    "  specify\n"
    "    if (mode)  (a => y) = 21;\n"
    "    if (!mode) (a => y) = 22;\n"
    "    ifnone     (a => y) = 23;\n"
    "    (b => z) = 24;\n"
    "    $setup(d, posedge clk &&& mode, 41, ntf);\n"
    "    $setup(d, posedge clk &&& !mode, 42, ntf);\n"
    "    $hold(posedge clk, d, 51, ntf);\n"
    "  endspecify\n"
    "endmodule\n";

// Locates one declared module path by everything §32.4.1 matches on: its two
// endpoint names plus the condition it was declared under.
inline const PathDelay* PathWith(const SpecifyManager& mgr,
                                 std::string_view src, std::string_view dst,
                                 std::string_view condition, bool is_ifnone) {
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == src && pd.dst_port == dst && pd.condition == condition &&
        pd.is_ifnone == is_ifnone) {
      return &pd;
    }
  }
  return nullptr;
}

inline const PathDelay* IfMode(const SpecifyManager& mgr) {
  return PathWith(mgr, "a", "y", "mode", false);
}
inline const PathDelay* IfNotMode(const SpecifyManager& mgr) {
  return PathWith(mgr, "a", "y", "!mode", false);
}
inline const PathDelay* Ifnone(const SpecifyManager& mgr) {
  return PathWith(mgr, "a", "y", "", true);
}
inline const PathDelay* BToZ(const SpecifyManager& mgr) {
  return PathWith(mgr, "b", "z", "", false);
}

// Reads back one declared timing check by type and by the condition it was
// declared under, which together are what an SDF timing check has to match.
inline const TimingCheckEntry* CheckWith(const SpecifyManager& mgr,
                                         TimingCheckKind kind,
                                         std::string_view condition) {
  for (const auto& tc : mgr.GetTimingChecks()) {
    if (tc.kind == kind && tc.condition == condition) return &tc;
  }
  return nullptr;
}

// Reads back the delays recorded for the primitive driving `output`.
inline const PrimitiveDriver* DriverOf(const SpecifyManager& mgr,
                                       std::string_view output) {
  for (const auto& drv : mgr.GetPrimitiveDrivers()) {
    if (drv.output_port == output) return &drv;
  }
  return nullptr;
}

// Parses |sdf| and annotates it onto an already-populated manager.
inline SdfAnnotationResult AnnotateFileOnto(const std::string& sdf,
                                            SpecifyManager& mgr) {
  SdfFile file;
  EXPECT_TRUE(ParseSdf(sdf, file));
  return AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
}

// Wraps one DELAY-section body in the surrounding SDF a cell needs.
inline std::string DelaySdf(const std::string& entries) {
  return "(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1) (DELAY (ABSOLUTE " +
         entries + ")))) ";
}

// Wraps one TIMINGCHECK-section body the same way.
inline std::string TimingCheckSdf(const std::string& entries) {
  return "(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1) (TIMINGCHECK " +
         entries + "))) ";
}
