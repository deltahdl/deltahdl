#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_scratch_dir.h"
#include "parser/ast_design.h"
#include "parser/precompiled_library.h"
#include "preprocessor/protect_license.h"

using namespace delta;

namespace {

constexpr std::string_view kModel = "module sealed_m;\nendmodule\n";

ProtectLicense Stating(std::string_view feature, uint64_t match) {
  ProtectLicense license;
  license.library = "liblic.so";
  license.entry = "checkout";
  license.feature = std::string(feature);
  license.exit = "checkin";
  license.has_exit = true;
  license.match = match;
  license.has_match = true;
  license.stated = true;
  return license;
}

void Precompile(const std::filesystem::path& path,
                std::vector<ProtectLicense> licenses) {
  PrecompiledDirectives directives;
  directives.runtime_licenses = std::move(licenses);
  ASSERT_TRUE(PrecompiledLibrary::Save(kModel, "ip", path, directives));
}

TEST(PrecompiledRuntimeLicense, EachPartComesBack) {
  ScratchDir tmp;
  auto path = tmp.dir / "ip.dpl";
  Precompile(path, {Stating("simulate", 42)});
  std::vector<ProtectLicense> read = PrecompiledLibrary::RuntimeLicenses(path);
  ASSERT_EQ(read.size(), 1u);
  EXPECT_EQ(read[0].library, "liblic.so");
  EXPECT_EQ(read[0].entry, "checkout");
  EXPECT_EQ(read[0].feature, "simulate");
  EXPECT_EQ(read[0].exit, "checkin");
  EXPECT_TRUE(read[0].has_exit);
  EXPECT_EQ(read[0].match, 42u);
  EXPECT_TRUE(read[0].has_match);
  EXPECT_TRUE(read[0].stated);
}

TEST(PrecompiledRuntimeLicense, AnUnwrittenExitAndMatchStayUnwritten) {
  ScratchDir tmp;
  auto path = tmp.dir / "ip.dpl";
  ProtectLicense license = Stating("simulate", 0);
  license.exit.clear();
  license.has_exit = false;
  license.has_match = false;
  Precompile(path, {license});
  std::vector<ProtectLicense> read = PrecompiledLibrary::RuntimeLicenses(path);
  ASSERT_EQ(read.size(), 1u);
  EXPECT_FALSE(read[0].has_exit);
  EXPECT_FALSE(read[0].has_match);
  EXPECT_EQ(read[0].match, 0u);
}

TEST(PrecompiledRuntimeLicense, EveryRecordsLicencesComeBackInOrder) {
  ScratchDir tmp;
  auto path = tmp.dir / "ip.dpl";
  Precompile(path, {Stating("simulate", 1), Stating("synthesize", 2)});
  Precompile(path, {Stating("emulate", 3)});
  std::vector<ProtectLicense> read = PrecompiledLibrary::RuntimeLicenses(path);
  ASSERT_EQ(read.size(), 3u);
  EXPECT_EQ(read[0].feature, "simulate");
  EXPECT_EQ(read[1].feature, "synthesize");
  EXPECT_EQ(read[2].feature, "emulate");
}

TEST(PrecompiledRuntimeLicense, AModelStatingNoneHasNone) {
  ScratchDir tmp;
  auto path = tmp.dir / "ip.dpl";
  Precompile(path, {});
  EXPECT_TRUE(PrecompiledLibrary::RuntimeLicenses(path).empty());
}

TEST(PrecompiledRuntimeLicense, AFileThisToolDidNotWriteHasNone) {
  ScratchDir tmp;
  auto path = tmp.dir / "ip.dpl";
  std::ofstream(path) << "not a compiled form\n";
  EXPECT_TRUE(PrecompiledLibrary::RuntimeLicenses(path).empty());
}

TEST(PrecompiledRuntimeLicense, ADamagedRecordHasNone) {
  ScratchDir tmp;
  auto path = tmp.dir / "ip.dpl";
  Precompile(path, {Stating("simulate", 42)});
  std::filesystem::resize_file(path, std::filesystem::file_size(path) - 3);
  EXPECT_TRUE(PrecompiledLibrary::RuntimeLicenses(path).empty());
}

TEST(PrecompiledRuntimeLicense, TheCellsBesideTheLicencesStillLoad) {
  ScratchDir tmp;
  auto path = tmp.dir / "ip.dpl";
  Precompile(path, {Stating("simulate", 42)});
  Precompile(path, {Stating("emulate", 7)});
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  CompilationUnit unit;
  ASSERT_TRUE(PrecompiledLibrary::Load(path, unit, mgr, arena, diag));
  ASSERT_EQ(unit.modules.size(), 1u);
  EXPECT_EQ(unit.modules[0]->name, "sealed_m");
}

}  // namespace
