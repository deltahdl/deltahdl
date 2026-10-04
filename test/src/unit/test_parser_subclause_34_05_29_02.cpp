// §34.5.29.2 runtime_license, Description, across a separate compilation.
//
// The licence an encrypted model states is asked before the model is executed,
// and §33.5.3 and §33.5.4 have the model precompiled by one invocation and
// executed by a later one that binds it. So the compiled form keeps each
// runtime licence the precompiled source stated beside the text it came with
// (PrecompiledDirectives::runtime_licenses), and PrecompiledLibrary::
// RuntimeLicenses reads them back for the binding invocation to ask.

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

// A licence stating each of its five parts, the feature and the match value
// as given.
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

// The compiled form at `path` gains one record of the model, stating
// `licenses`.
void Precompile(const std::filesystem::path& path,
                std::vector<ProtectLicense> licenses) {
  PrecompiledDirectives directives;
  directives.runtime_licenses = std::move(licenses);
  ASSERT_TRUE(PrecompiledLibrary::Save(kModel, "ip", path, directives));
}

// Every part of the licence comes back as it was precompiled.
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

// A licence naming no exit function and writing no match value comes back
// naming none and held to 0, which is what §34.5.28.2 asks of it.
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

// The licences of every record come back, in the order they were precompiled.
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

// A model stating no licence leaves none to ask.
TEST(PrecompiledRuntimeLicense, AModelStatingNoneHasNone) {
  ScratchDir tmp;
  auto path = tmp.dir / "ip.dpl";
  Precompile(path, {});
  EXPECT_TRUE(PrecompiledLibrary::RuntimeLicenses(path).empty());
}

// A file this tool did not write holds no licence it can read.
TEST(PrecompiledRuntimeLicense, AFileThisToolDidNotWriteHasNone) {
  ScratchDir tmp;
  auto path = tmp.dir / "ip.dpl";
  std::ofstream(path) << "not a compiled form\n";
  EXPECT_TRUE(PrecompiledLibrary::RuntimeLicenses(path).empty());
}

// A damaged record leaves none to ask, as it leaves no cells to load.
TEST(PrecompiledRuntimeLicense, ADamagedRecordHasNone) {
  ScratchDir tmp;
  auto path = tmp.dir / "ip.dpl";
  Precompile(path, {Stating("simulate", 42)});
  std::filesystem::resize_file(path, std::filesystem::file_size(path) - 3);
  EXPECT_TRUE(PrecompiledLibrary::RuntimeLicenses(path).empty());
}

// The cells of a record stating licences still load, so the licences are read
// past rather than taken for the next record.
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
