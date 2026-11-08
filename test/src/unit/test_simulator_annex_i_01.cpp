#include <gtest/gtest.h>

#include <array>
#include <string_view>
#include <type_traits>

#include "simulator/dpi_include_file.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

TEST(SvdpiHContents, TheAnnexListsThreeKindsOfContent) {
  EXPECT_EQ(DpiAnnexListingSvdpiH(), "Annex I");
  const std::array<DpiSvdpiContent, 3> kContents = DpiSvdpiContents();
  EXPECT_EQ(kContents[0], DpiSvdpiContent::kConstantDefinitions);
  EXPECT_EQ(kContents[1], DpiSvdpiContent::kStructureDefinitions);
  EXPECT_EQ(kContents[2], DpiSvdpiContent::kRoutineDeclarations);
  for (DpiSvdpiContent content : kContents) {
    EXPECT_TRUE(DpiSvdpiHContains(content));
  }
}

TEST(SvdpiHContents, TheFileProvidesConstantsStructuresAndRoutines) {
  EXPECT_EQ(sv_x, 3);
  EXPECT_EQ(sv_scaled_real_time, 1);
  svLogicVecVal chunk = {};
  chunk.aval = 1;
  chunk.bval = 1;
  EXPECT_EQ(chunk.aval + chunk.bval, 2u);
  svTimeVal time = {};
  time.type = sv_sim_time;
  EXPECT_EQ(time.type, sv_sim_time);
  EXPECT_TRUE((std::is_same<decltype(svDpiVersion()), const char*>::value));
  EXPECT_GT(sizeof(&svGetScope), 0u);
}

}  // namespace
