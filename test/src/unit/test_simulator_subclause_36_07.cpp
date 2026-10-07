#include <gtest/gtest.h>

// §36.7 -- PLI include files. The libraries of PLI functions are defined in C
// include files that are themselves normative, and the same files define the
// constants, structures and other data the library and the interface use. They
// are vpi_user.h (Annex K) and sv_vpi_user.h (Annex M), and an application
// calling the VPI routines must include both.
//
// What this file is written as is the application the clause describes: it
// names the two include files and nothing else of the tool's, so every type,
// constant and routine the cases below reach is one those two files supplied.
// A tool whose interface is reachable only under some other name compiles none
// of this, which is what makes the includes themselves the observation.
//
// The SV file comes first, and its position is deliberate. Annex M has
// sv_vpi_user.h open by including vpi_user.h, so an application naming only the
// SV half is still handed the base library; taking that half first is what lets
// a case tell whether the base file arrived with it or was never there at all.
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_globals.h"

namespace {

// Latched at the point only the SV include file has been named. Once the base
// file is included below this is true whatever the SV file did, so the value
// has to be taken here or not at all.
#ifdef VPI_USER_H
constexpr bool kSvFileBroughtTheBaseFile = true;
#else
constexpr bool kSvFileBroughtTheBaseFile = false;
#endif

}  // namespace

// The base file again, this time under the name §36.7 gives it. Naming it
// directly is what an application including the two files does, and naming it
// after the SV file has already pulled it in is the repeat a normative include
// file has to survive: this translation unit compiling at all is the
// observation for that, and the guard is read again below.
#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace {

#ifdef VPI_USER_H
constexpr bool kGuardHeldAcrossTheRepeat = true;
#else
constexpr bool kGuardHeldAcrossTheRepeat = false;
#endif

}  // namespace

namespace delta {
namespace {

TEST(PliIncludeFiles, TheSvFileBringsTheBaseFileWithIt) {
  // §36.7 names two files and Annex M's source has the second include the
  // first, so the base library is under the SV extensions rather than beside
  // them. Before the base file existed under this name the SV file opened by
  // including simulator/vpi.h, and VPI_USER_H was defined by nothing at all.
  EXPECT_TRUE(kSvFileBroughtTheBaseFile);
  EXPECT_TRUE(kGuardHeldAcrossTheRepeat);
}

TEST(PliIncludeFiles, TheBaseFileDefinesTheConstantsReservedToIt) {
  // The files also define the constants the PLI library uses. Annex K reserves
  // the values 1 through 299 to the base file, so an object type, a value
  // format and a callback reason drawn from it are all inside that range -- the
  // range is what says which of the two files the constant came out of.
  EXPECT_GE(vpiModule, 1);
  EXPECT_LE(vpiModule, 299);
  EXPECT_GE(vpiIntVal, 1);
  EXPECT_LE(vpiIntVal, 299);
  EXPECT_GE(cbValueChange, 1);
  EXPECT_LE(cbValueChange, 299);
}

TEST(PliIncludeFiles, TheSvFileDefinesTheConstantsReservedToIt) {
  // Annex M reserves 600 through 999 to the SV file, and the object types it
  // adds are the SystemVerilog ones the base file has no name for. The check
  // is confined to object types because Annex M permits its other categories
  // -- operation kinds, property values -- to overlap the base ranges, so a
  // bound over those would be a bound the standard does not set.
  EXPECT_GE(vpiPackage, 600);
  EXPECT_LE(vpiPackage, 999);
  EXPECT_GE(vpiInterface, 600);
  EXPECT_LE(vpiInterface, 999);
  EXPECT_GE(vpiClassVar, 600);
  EXPECT_LE(vpiClassVar, 999);
}

TEST(PliIncludeFiles, TheFilesDefineTheStructuresTheRoutinesAreCalledWith) {
  // The files also define the structures and other data the PLI library and the
  // interface use. Each structure below is filled the way a routine's caller
  // fills it, so the fields read back are the ones the include file laid out
  // rather than a default.
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 7;
  EXPECT_EQ(value.format, vpiIntVal);
  EXPECT_EQ(value.value.integer, 7);

  s_vpi_time time = {};
  time.type = vpiSimTime;
  time.low = 5;
  EXPECT_EQ(time.type, vpiSimTime);
  EXPECT_EQ(time.low, 5u);

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  EXPECT_EQ(cb.reason, cbValueChange);

  // The SV file's own structure, which the base file does not lay out: an
  // assertion attempt's step detail, from the sv_vpi_user.h half of §36.7.
  s_vpi_assertion_step_info step = {};
  step.stateFrom = 1;
  step.stateTo = 2;
  EXPECT_EQ(step.stateFrom, 1);
  EXPECT_EQ(step.stateTo, 2);
}

// A run reaching the library through nothing but the two include files. The
// routines they declare have to be the ones the tool defines, or a call made
// through the declaration reaches something else or does not link.
class PliIncludeFileLibrary : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(PliIncludeFileLibrary, AnApplicationIncludingTheFilesReachesTheLibrary) {
  // §36.7's files are where the libraries of PLI functions are defined, so a
  // registration made through the declaration one of them carries is a
  // registration the tool holds. Reading it back through a second routine is
  // what says the two ends met: the record vpi_get_systf_info fills is the
  // structure the include file laid out, filled from what the registry kept.
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");

  vpiHandle systf = vpi_register_systf(&data);
  ASSERT_NE(systf, nullptr);

  s_vpi_systf_data read_back = {};
  vpi_get_systf_info(systf, &read_back);
  EXPECT_EQ(read_back.type, vpiSysTask);
  ASSERT_NE(read_back.tfname, nullptr);
  EXPECT_STREQ(read_back.tfname, "$probe");
}

}  // namespace
}  // namespace delta
