#include <gtest/gtest.h>

#include <cmath>
#include <cstddef>
#include <cstdint>
#include <ostream>
#include <string>
#include <type_traits>
#include <vector>

#include "elaborator/elaborator.h"
#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "helpers_dpi_c_binding.h"
#include "helpers_dpi_scope_names.h"
#include "preprocessor/preprocessor.h"
#include "simulator/svdpi.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct TimesOfAScope {
  double now = -1.0;
  int32_t unit = 99;
  int32_t precision = 99;

  bool operator==(const TimesOfAScope&) const = default;
};

void PrintTo(const TimesOfAScope& times, std::ostream* out) {
  *out << times.now << " in " << times.unit << "/" << times.precision;
}

TimesOfAScope TimesOf(svScope scope) {
  TimesOfAScope times;
  svTimeVal time = {};
  time.type = sv_scaled_real_time;
  if (svGetTime(scope, &time) == 0) {
    times.now = std::round(time.real * 1e9) / 1e9;
  }
  svGetTimeUnit(scope, &times.unit);
  svGetTimePrecision(scope, &times.precision);
  return times;
}

std::vector<TimesOfAScope>& TimesSeen() {
  static std::vector<TimesOfAScope> seen;
  return seen;
}

void SeeTimesOfItsScope() { TimesSeen().push_back(TimesOf(svGetScope())); }

void SeeTimesOfNoScope() { TimesSeen().push_back(TimesOf(nullptr)); }

void SeeTimesOfTheSlowInstance() {
  svScope slow = svGetScopeFromName("top.slow");
  SeeInC({static_cast<long long>(slow != nullptr)});
  if (slow != nullptr) TimesSeen().push_back(TimesOf(slow));
}

void SeeRawTimes() {
  for (svScope scope : {svGetScope(), svScope{nullptr}}) {
    svTimeVal time = {};
    time.type = sv_sim_time;
    svGetTime(scope, &time);
    SeeInC({time.high, time.low});
  }
}

void SeeVpiPropertiesOfItsScope() {
  svScope scope = svGetScope();
  const char* name = svGetNameFromScope(scope);
  vpiHandle instance =
      name == nullptr ? nullptr : vpi_handle_by_name(VpiText(name), nullptr);
  TimesOfAScope times = TimesOf(scope);
  SeeInC({static_cast<long long>(instance != nullptr), times.unit,
          vpi_get(vpiTimeUnit, instance), times.precision,
          vpi_get(vpiTimePrecision, instance)});
}

class ScopeTimesOfADesign : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    TimesSeen().clear();
  }

  std::vector<TimesOfAScope> TimesOfRun(const std::string& src,
                                        const std::string& dir_name) {
    RunDesignWithC(src, f_,
                   {{"see", CAddress(&SeeTimesOfItsScope)},
                    {"see_none", CAddress(&SeeTimesOfNoScope)},
                    {"see_slow", CAddress(&SeeTimesOfTheSlowInstance)},
                    {"see_raw", CAddress(&SeeRawTimes)},
                    {"see_vpi", CAddress(&SeeVpiPropertiesOfItsScope)}},
                   dir_name);
    return TimesSeen();
  }
};

constexpr const char* kTwoTimescales =
    "module slow_m;\n"
    "  timeunit 1us/100ps;\n"
    "  import \"DPI-C\" context function void see();\n"
    "  import \"DPI-C\" context function void see_raw();\n"
    "  import \"DPI-C\" context function void see_vpi();\n"
    "endmodule\n"
    "module top;\n"
    "  timeunit 1ns/1ps;\n"
    "  import \"DPI-C\" context function void see();\n"
    "  import \"DPI-C\" context function void see_none();\n"
    "  import \"DPI-C\" context function void see_slow();\n"
    "  import \"DPI-C\" context function void see_raw();\n"
    "  import \"DPI-C\" context function void see_vpi();\n"
    "  slow_m slow();\n";

std::string SlowAndTop(const std::string& slow, const std::string& top) {
  std::string src = kTwoTimescales;
  const std::size_t kEnd = src.find("endmodule");
  src.insert(kEnd, "  initial #0.0025 " + slow + ";\n");
  return src + "  initial #2.5 " + top + ";\nendmodule\n";
}

TEST_F(ScopeTimesOfADesign, DISABLED_AModulesTimescaleIsThatOfItsScope) {
  EXPECT_EQ(TimesOfRun(SlowAndTop("", "see()"), "annex_h_13_top"),
            (std::vector<TimesOfAScope>{{2.5, -9, -12}}));
}

TEST_F(ScopeTimesOfADesign, DISABLED_EachInstanceReadsItsOwnTimescale) {
  EXPECT_EQ(TimesOfRun(SlowAndTop("see()", ""), "annex_h_13_slow"),
            (std::vector<TimesOfAScope>{{0.0025, -6, -10}}));
}

TEST_F(ScopeTimesOfADesign, DISABLED_AScopeFoundByNameReadsItsOwnTimescale) {
  EXPECT_EQ(TimesOfRun(SlowAndTop("", "see_slow()"), "annex_h_13_name"),
            (std::vector<TimesOfAScope>{{0.0025, -6, -10}}));
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1}));
}

TEST_F(ScopeTimesOfADesign, NoScopeReadsTheSmallestPrecision) {
  EXPECT_EQ(TimesOfRun(SlowAndTop("", "see_none()"), "annex_h_13_none"),
            (std::vector<TimesOfAScope>{{2500.0, -12, -12}}));
}

TEST_F(ScopeTimesOfADesign, SimulationTimeIsTheCountInEveryScope) {
  TimesOfRun(SlowAndTop("", "see_raw()"), "annex_h_13_raw");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0, 2500, 0, 2500}));
}

TEST_F(ScopeTimesOfADesign, SimulationTimeIsTheCountInACoarseScope) {
  TimesOfRun(SlowAndTop("see_raw()", ""), "annex_h_13_raw_slow");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0, 2500, 0, 2500}));
}

TEST_F(ScopeTimesOfADesign, DISABLED_AScopeAgreesWithItsModulesProperties) {
  TimesOfRun(SlowAndTop("", "see_vpi()"), "annex_h_13_vpi");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, -9, -9, -12, -12}));
}

TEST_F(ScopeTimesOfADesign, DISABLED_AScopeAgreesWithItsInstancesProperties) {
  TimesOfRun(SlowAndTop("see_vpi()", ""), "annex_h_13_vpi_slow");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, -6, -6, -10, -10}));
}

TEST_F(ScopeTimesOfADesign, DISABLED_ADeclaredTimeUnitIsThatOfItsScope) {
  EXPECT_EQ(TimesOfRun("module top;\n"
                       "  timeunit 10ns;\n"
                       "  timeprecision 100ps;\n"
                       "  import \"DPI-C\" context function void see();\n"
                       "  initial #2.5 see();\n"
                       "endmodule\n",
                       "annex_h_13_declared"),
            (std::vector<TimesOfAScope>{{2.5, -8, -10}}));
}

TEST_F(ScopeTimesOfADesign, DISABLED_ADirectivesTimeUnitIsThatOfItsScope) {
  auto fid = f_.mgr.AddFile("<test>",
                            "`timescale 10ns/100ps\n"
                            "module top;\n"
                            "  import \"DPI-C\" context function void see();\n"
                            "  initial #2.5 see();\n"
                            "endmodule\n");
  Preprocessor preprocessor(f_.mgr, f_.diag, {});
  auto* unit = PreprocessAndParseCu(f_, fid, preprocessor);
  PropagateDirectivesToCu(unit, preprocessor);
  Elaborator elaborator(f_.arena, f_.diag, unit);
  RunDesignWithImportsBound(elaborator.Elaborate("top"), f_,
                            {{"see", CAddress(&SeeTimesOfItsScope)}},
                            "annex_h_13_directive");
  EXPECT_TRUE(f_.diag.Diagnostics().empty());
  EXPECT_EQ(TimesSeen(), (std::vector<TimesOfAScope>{{2.5, -8, -10}}));
}

TEST_F(ScopeTimesOfADesign, DISABLED_AnInterfaceReadsItsOwnTimeUnit) {
  EXPECT_EQ(TimesOfRun("interface ifc;\n"
                       "  timeunit 1us;\n"
                       "  timeprecision 1ns;\n"
                       "  import \"DPI-C\" context function void see();\n"
                       "  initial #0.25 see();\n"
                       "endinterface\n"
                       "module top;\n"
                       "  timeunit 1ns;\n"
                       "  timeprecision 1ps;\n"
                       "  ifc i();\n"
                       "endmodule\n",
                       "annex_h_13_interface"),
            (std::vector<TimesOfAScope>{{0.25, -6, -9}}));
}

TEST_F(ScopeTimesOfADesign, DISABLED_AProgramReadsItsOwnTimeUnit) {
  EXPECT_EQ(TimesOfRun("program prg;\n"
                       "  timeunit 1us;\n"
                       "  timeprecision 1ns;\n"
                       "  import \"DPI-C\" context function void see();\n"
                       "  initial #0.25 see();\n"
                       "endprogram\n"
                       "module top;\n"
                       "  timeunit 1ns;\n"
                       "  timeprecision 1ps;\n"
                       "  prg p();\n"
                       "endmodule\n",
                       "annex_h_13_program"),
            (std::vector<TimesOfAScope>{{0.25, -6, -9}}));
}

TEST_F(ScopeTimesOfADesign, DISABLED_APackageReadsItsOwnTimeUnit) {
  EXPECT_EQ(TimesOfRun("package pk;\n"
                       "  timeunit 1us;\n"
                       "  timeprecision 1ns;\n"
                       "  import \"DPI-C\" context function void see();\n"
                       "endpackage\n"
                       "module top;\n"
                       "  timeunit 1ns;\n"
                       "  timeprecision 1ps;\n"
                       "  initial #250 pk::see();\n"
                       "endmodule\n",
                       "annex_h_13_package"),
            (std::vector<TimesOfAScope>{{0.25, -6, -9}}));
}

TEST_F(ScopeTimesOfADesign, DISABLED_AModuleTakesTheUnitsTimeUnit) {
  EXPECT_EQ(TimesOfRun("timeunit 1us;\n"
                       "timeprecision 1ns;\n"
                       "module other;\n"
                       "  timeunit 1ns;\n"
                       "  timeprecision 1ps;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  import \"DPI-C\" context function void see();\n"
                       "  other o();\n"
                       "  initial #0.25 see();\n"
                       "endmodule\n",
                       "annex_h_13_unit"),
            (std::vector<TimesOfAScope>{{0.25, -6, -9}}));
}

TEST(TimeInADesign, DISABLED_TheTimeIsReadWithoutAVpiApplication) {
  SimFixture f;
  TimesSeen().clear();
  RunDesignWithC(
      "module top;\n"
      "  timeunit 1ns/1ps;\n"
      "  import \"DPI-C\" context function void see_none();\n"
      "  import \"DPI-C\" context function void see_raw();\n"
      "  initial #2.5 begin see_none(); see_raw(); end\n"
      "endmodule\n",
      f,
      {{"see_none", CAddress(&SeeTimesOfNoScope)},
       {"see_raw", CAddress(&SeeRawTimes)}},
      "annex_h_13_no_vpi");
  EXPECT_EQ(TimesSeen(), (std::vector<TimesOfAScope>{{2500.0, -12, -12}}));
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0, 2500, 0, 2500}));
}

TEST(TimeInADesign, TheTimeStructureIsThatOfVpi) {
  EXPECT_TRUE((std::is_same_v<svTimeVal, s_vpi_time>));
  EXPECT_EQ(sv_scaled_real_time, vpiScaledRealTime);
  EXPECT_EQ(sv_sim_time, vpiSimTime);
}

TEST(TimeInADesign, TheFunctionsHaveTheirPrototypes) {
  EXPECT_TRUE((std::is_same_v<decltype(svGetTime), int(svScope, svTimeVal*)>));
  EXPECT_TRUE((std::is_same_v<decltype(svGetTimeUnit), int(svScope, int*)>));
  EXPECT_TRUE(
      (std::is_same_v<decltype(svGetTimePrecision), int(svScope, int*)>));
}

}  // namespace
}  // namespace delta
