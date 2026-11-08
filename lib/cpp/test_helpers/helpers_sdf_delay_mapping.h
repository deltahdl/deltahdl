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

inline bool BuildSpecifyFromSource(const std::string& src, SimFixture& f,
                                   SpecifyManager& mgr) {
  auto* cu = RunModuleSource(src, f);
  if (cu == nullptr) return false;
  const ModuleDecl& mod = *cu->modules.back();
  RegisterPrimitiveDrivers(mod, f, mgr);
  RegisterPathDelays(mod, f, mgr, true);
  RegisterTimingChecks(mod, f, mgr);
  RegisterPathPulseSpecparams(mod, f, mgr);
  return true;
}

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

inline const TimingCheckEntry* CheckWith(const SpecifyManager& mgr,
                                         TimingCheckKind kind,
                                         std::string_view condition) {
  for (const auto& tc : mgr.GetTimingChecks()) {
    if (tc.kind == kind && tc.condition == condition) return &tc;
  }
  return nullptr;
}

inline const PrimitiveDriver* DriverOf(const SpecifyManager& mgr,
                                       std::string_view output) {
  for (const auto& drv : mgr.GetPrimitiveDrivers()) {
    if (drv.output_port == output) return &drv;
  }
  return nullptr;
}

inline SdfAnnotationResult AnnotateFileOnto(const std::string& sdf,
                                            SpecifyManager& mgr) {
  SdfFile file;
  EXPECT_TRUE(ParseSdf(sdf, file));
  return AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
}

inline std::string DelaySdf(const std::string& entries) {
  return "(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1) (DELAY (ABSOLUTE " +
         entries + ")))) ";
}

inline std::string TimingCheckSdf(const std::string& entries) {
  return "(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1) (TIMINGCHECK " +
         entries + "))) ";
}
