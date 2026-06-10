#include <gtest/gtest.h>

#include <cstring>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// A minimal simulator context for exercising the %l / %L display path. The
// format helper reads the running instance's recorded library.cell binding out
// of the SimContext, so the tests register bindings on this context directly.
struct BindingDisplayFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

TEST(LibraryBindingDisplay, FormatSpecifierLowerLProducesBindingInfo) {
  BindingDisplayFixture fx;
  // With no running process the containing instance is the top, keyed by the
  // empty prefix; %l reports its resolved library.cell.
  fx.ctx.RegisterInstanceBinding("", "rtlLib", "adder");
  std::vector<Logic4Vec> vals;
  auto out = FormatDisplay("%l", vals, {}, nullptr, {}, &fx.ctx);
  EXPECT_EQ(out, "rtlLib.adder");
}

TEST(LibraryBindingDisplay, FormatSpecifierUpperLProducesBindingInfo) {
  BindingDisplayFixture fx;
  fx.ctx.RegisterInstanceBinding("", "rtlLib", "adder");
  std::vector<Logic4Vec> vals;
  // %L is the same specifier as %l and reports the same binding.
  auto out = FormatDisplay("%L", vals, {}, nullptr, {}, &fx.ctx);
  EXPECT_EQ(out, "rtlLib.adder");
}

TEST(LibraryBindingDisplay, FormatSpecifierLDoesNotConsumeArg) {
  BindingDisplayFixture fx;
  fx.ctx.RegisterInstanceBinding("", "rtlLib", "adder");
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(fx.arena, 8, 42)};
  auto out = FormatDisplay("%l %d", vals, {}, nullptr, {}, &fx.ctx);
  // %l takes no argument (like %m), so the following %d still renders the value.
  EXPECT_NE(out.find("rtlLib.adder"), std::string::npos);
  EXPECT_NE(out.find("42"), std::string::npos);
}

TEST(LibraryBindingDisplay, FormatSpecifierLSelectsContainingInstanceBinding) {
  BindingDisplayFixture fx;
  // Two instances with different bindings; the running process sits inside the
  // child, so %l must report the child's binding, not the top's -- the same
  // "instance containing the command" rule %m follows.
  fx.ctx.RegisterInstanceBinding("", "rtlLib", "top");
  fx.ctx.RegisterInstanceBinding("a2", "gateLib", "adder");
  Process proc;
  proc.inst_prefix = "a2.";
  fx.ctx.SetCurrentProcess(&proc);
  std::vector<Logic4Vec> vals;
  auto out = FormatDisplay("%l", vals, {}, nullptr, {}, &fx.ctx);
  fx.ctx.SetCurrentProcess(nullptr);
  EXPECT_EQ(out, "gateLib.adder");
}

TEST(LibraryBindingDisplay, FormatSpecifierLFallsBackWhenInstanceHasNoBinding) {
  BindingDisplayFixture fx;  // no binding registered for any instance
  std::vector<Logic4Vec> vals;
  // With no recorded binding for the containing instance, %l still substitutes
  // a non-empty library.cell-shaped token between the surrounding literal text
  // rather than vanishing.
  auto out = FormatDisplay("x%ly", vals, {}, nullptr, {}, &fx.ctx);
  EXPECT_EQ(out.front(), 'x');
  EXPECT_EQ(out.back(), 'y');
  EXPECT_NE(out.find('.'), std::string::npos);
  EXPECT_GT(out.size(), 2u);
}

TEST(LibraryBindingDisplay, VpiBindingPropertyConstantsAreDistinct) {
  EXPECT_NE(kVpiLibrary, kVpiCell);
  EXPECT_NE(kVpiLibrary, kVpiConfig);
  EXPECT_NE(kVpiCell, kVpiConfig);
  EXPECT_NE(kVpiLibrary, kVpiName);
  EXPECT_NE(kVpiCell, kVpiName);
  EXPECT_NE(kVpiConfig, kVpiName);
}

TEST(LibraryBindingDisplay, VpiGetStrReturnsLibraryNameForModule) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("adder", "top.a2");
  mod->library_name = "gateLib";
  const char* lib = ctx.GetStr(kVpiLibrary, mod);
  ASSERT_NE(lib, nullptr);
  EXPECT_STREQ(lib, "gateLib");
}

TEST(LibraryBindingDisplay, VpiGetStrReturnsCellNameForModule) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("adder", "top.a2");
  mod->cell_name = "adder";
  const char* cell = ctx.GetStr(kVpiCell, mod);
  ASSERT_NE(cell, nullptr);
  EXPECT_STREQ(cell, "adder");
}

TEST(LibraryBindingDisplay, VpiGetStrReturnsConfigNameForModule) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("adder", "top.a2");
  mod->config_name = "work.cfg5";
  const char* cfg = ctx.GetStr(kVpiConfig, mod);
  ASSERT_NE(cfg, nullptr);
  EXPECT_STREQ(cfg, "work.cfg5");
}

TEST(LibraryBindingDisplay, VpiBindingPropertiesReturnStringWhenUnset) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("m", "m");
  EXPECT_NE(ctx.GetStr(kVpiLibrary, mod), nullptr);
  EXPECT_NE(ctx.GetStr(kVpiConfig, mod), nullptr);

  EXPECT_NE(ctx.GetStr(kVpiCell, mod), nullptr);
}

TEST(LibraryBindingDisplay, VpiBindingPropertiesAreModuleScoped) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("top", "top");
  VpiHandle port = ctx.CreatePort("p", kVpiInput, mod);
  EXPECT_EQ(ctx.GetStr(kVpiLibrary, port), nullptr);
  EXPECT_EQ(ctx.GetStr(kVpiCell, port), nullptr);
  EXPECT_EQ(ctx.GetStr(kVpiConfig, port), nullptr);
}

TEST(LibraryBindingDisplay, VpiBindingPropertiesAreNullSafe) {
  VpiContext ctx;
  EXPECT_EQ(ctx.GetStr(kVpiLibrary, nullptr), nullptr);
  EXPECT_EQ(ctx.GetStr(kVpiCell, nullptr), nullptr);
  EXPECT_EQ(ctx.GetStr(kVpiConfig, nullptr), nullptr);
}

TEST(LibraryBindingDisplay, VpiGetStrCApiReadsBindingProperties) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  VpiHandle mod = ctx.CreateModule("adder", "top.a1");
  mod->library_name = "rtlLib";
  mod->cell_name = "adder";
  mod->config_name = "work.cfg1";
  EXPECT_STREQ(vpi_get_str(vpiLibrary, mod), "rtlLib");
  EXPECT_STREQ(vpi_get_str(vpiCell, mod), "adder");
  EXPECT_STREQ(vpi_get_str(vpiConfig, mod), "work.cfg1");
  SetGlobalVpiContext(nullptr);
}

}
}
