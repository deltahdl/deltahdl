#include <gtest/gtest.h>

#include <cstring>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/evaluation.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §33.7: %l shall print library.cell binding info for the containing module.
TEST(LibraryBindingDisplay, FormatSpecifierLowerLProducesBindingInfo) {
  std::vector<Logic4Vec> vals;
  auto out = FormatDisplay("%l", vals);
  EXPECT_FALSE(out.empty());
}

// §33.7: %L is an alias for %l.
TEST(LibraryBindingDisplay, FormatSpecifierUpperLProducesBindingInfo) {
  std::vector<Logic4Vec> vals;
  auto out = FormatDisplay("%L", vals);
  EXPECT_FALSE(out.empty());
}

// %l does not consume an argument (like %m); it can appear alongside other
// specifiers without shifting their positional binding.
TEST(LibraryBindingDisplay, FormatSpecifierLDoesNotConsumeArg) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 8, 42)};
  auto out = FormatDisplay("%l %d", vals);
  EXPECT_NE(out.find("42"), std::string::npos);
}

// §33.7: vpiLibrary, vpiCell, vpiConfig constants must exist and be distinct.
TEST(LibraryBindingDisplay, VpiBindingPropertyConstantsAreDistinct) {
  EXPECT_NE(kVpiLibrary, kVpiCell);
  EXPECT_NE(kVpiLibrary, kVpiConfig);
  EXPECT_NE(kVpiCell, kVpiConfig);
  EXPECT_NE(kVpiLibrary, kVpiName);
  EXPECT_NE(kVpiCell, kVpiName);
  EXPECT_NE(kVpiConfig, kVpiName);
}

// §33.7: vpi_get_str on vpiModule shall return the library name string.
TEST(LibraryBindingDisplay, VpiGetStrReturnsLibraryNameForModule) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("adder", "top.a2");
  mod->library_name = "gateLib";
  const char* lib = ctx.GetStr(kVpiLibrary, mod);
  ASSERT_NE(lib, nullptr);
  EXPECT_STREQ(lib, "gateLib");
}

// §33.7: vpi_get_str on vpiModule shall return the cell name string.
TEST(LibraryBindingDisplay, VpiGetStrReturnsCellNameForModule) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("adder", "top.a2");
  mod->cell_name = "adder";
  const char* cell = ctx.GetStr(kVpiCell, mod);
  ASSERT_NE(cell, nullptr);
  EXPECT_STREQ(cell, "adder");
}

// §33.7: vpi_get_str on vpiModule shall return the config name string in
// library.cell form.
TEST(LibraryBindingDisplay, VpiGetStrReturnsConfigNameForModule) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("adder", "top.a2");
  mod->config_name = "work.cfg5";
  const char* cfg = ctx.GetStr(kVpiConfig, mod);
  ASSERT_NE(cfg, nullptr);
  EXPECT_STREQ(cfg, "work.cfg5");
}

// §33.7: when no binding info has been set, the property shall still return
// a string (not nullptr) -- it is a string-typed property.
TEST(LibraryBindingDisplay, VpiBindingPropertiesReturnStringWhenUnset) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("m", "m");
  EXPECT_NE(ctx.GetStr(kVpiLibrary, mod), nullptr);
  EXPECT_NE(ctx.GetStr(kVpiConfig, mod), nullptr);
  // vpiCell defaults to the cell-bound name, which is the module name.
  EXPECT_NE(ctx.GetStr(kVpiCell, mod), nullptr);
}

// %L (the upper-case variant) likewise does not consume a positional arg.
TEST(LibraryBindingDisplay, FormatSpecifierUpperLDoesNotConsumeArg) {
  Arena arena;
  std::vector<Logic4Vec> vals{MakeLogic4VecVal(arena, 8, 7)};
  auto out = FormatDisplay("%L %d", vals);
  EXPECT_NE(out.find("7"), std::string::npos);
}

// The binding marker integrates with surrounding literal text rather than
// swallowing it.
TEST(LibraryBindingDisplay, FormatSpecifierLPreservesSurroundingText) {
  std::vector<Logic4Vec> vals;
  auto out = FormatDisplay("before:%l:after", vals);
  EXPECT_NE(out.find("before:"), std::string::npos);
  EXPECT_NE(out.find(":after"), std::string::npos);
}

// Multiple %l occurrences in a single format string each emit a binding
// marker (idempotent dispatch, no state shared between specifiers).
TEST(LibraryBindingDisplay, FormatSpecifierLAppearsOncePerOccurrence) {
  std::vector<Logic4Vec> vals;
  auto first = FormatDisplay("%l", vals);
  ASSERT_FALSE(first.empty());
  auto twice = FormatDisplay("%l %l", vals);
  // Both occurrences expanded -- the doubled output contains the single
  // expansion at least twice.
  size_t pos = twice.find(first);
  ASSERT_NE(pos, std::string::npos);
  EXPECT_NE(twice.find(first, pos + 1), std::string::npos);
}

// §33.7 scopes the binding properties to "objects of type vpiModule"; they
// are not meaningful on ports, nets, or parameters.
TEST(LibraryBindingDisplay, VpiBindingPropertiesAreModuleScoped) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("top", "top");
  VpiHandle port = ctx.CreatePort("p", kVpiInput, mod);
  EXPECT_EQ(ctx.GetStr(kVpiLibrary, port), nullptr);
  EXPECT_EQ(ctx.GetStr(kVpiCell, port), nullptr);
  EXPECT_EQ(ctx.GetStr(kVpiConfig, port), nullptr);
}

// Defensive: a null handle yields a null result rather than dereferencing.
TEST(LibraryBindingDisplay, VpiBindingPropertiesAreNullSafe) {
  VpiContext ctx;
  EXPECT_EQ(ctx.GetStr(kVpiLibrary, nullptr), nullptr);
  EXPECT_EQ(ctx.GetStr(kVpiCell, nullptr), nullptr);
  EXPECT_EQ(ctx.GetStr(kVpiConfig, nullptr), nullptr);
}

// The C entry point vpi_get_str -- the surface §33.7 names as the way "to
// use VPI to display the binding information" -- is wired to the same
// dispatch as the C++ context method.
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

}  // namespace
}  // namespace delta
