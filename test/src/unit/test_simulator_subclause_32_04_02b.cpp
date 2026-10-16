#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

// §32.4.2 with the SDF format §32 annotates from (IEEE Std 1497): SETUP, HOLD
// and SETUPHOLD write their data signal first, but RECOVERY, REMOVAL, RECREM,
// SKEW, BIDIRECTSKEW and NOCHANGE write their reference signal first, in the
// order the SystemVerilog check they annotate takes its events. Each case below
// declares one check on two signals and annotates it from an entry naming the
// same two signals in the SDF order; read the other way round, the entry names
// a check with the two signals swapped, which the design does not declare, so
// the value lands nowhere and the annotator warns.
struct SdfReferenceFirstCheck : public ::testing::Test {
  SimFixture f;
  SpecifyManager mgr;

  // Declares `check` in a module on RN, CK, CK2 and D, annotates `entry` onto
  // it and returns the one check declared.
  const TimingCheckEntry& Annotate(const std::string& check,
                                   const std::string& entry) {
    auto* cu = RunModuleSource(
        "module t(input RN, input CK, input CK2, input D);\n"
        "  reg n;\n"
        "  specify\n"
        "    " +
            check +
            "\n"
            "  endspecify\n"
            "endmodule\n",
        f);
    EXPECT_NE(cu, nullptr);
    RegisterTimingChecks(*cu->modules.back(), f, mgr);
    SdfFile file;
    EXPECT_TRUE(ParseSdf(
        "(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1) (TIMINGCHECK " +
            entry + ")))",
        file));
    warnings = AnnotateSdfToManager(file, mgr, SdfMtm::kTypical).warnings;
    EXPECT_EQ(mgr.TimingCheckCount(), 1u);
    return mgr.GetTimingChecks()[0];
  }

  std::vector<std::string> warnings;
};

TEST_F(SdfReferenceFirstCheck, RecoveryReadsItsFirstSignalAsTheReference) {
  const TimingCheckEntry& tc =
      Annotate("$recovery(posedge RN, posedge CK, 3, n);",
               "(RECOVERY (posedge RN) (posedge CK) (7))");
  EXPECT_EQ(tc.limit, 7u);
  EXPECT_TRUE(warnings.empty());
}

TEST_F(SdfReferenceFirstCheck, RemovalReadsItsFirstSignalAsTheReference) {
  const TimingCheckEntry& tc =
      Annotate("$removal(posedge RN, posedge CK, 3, n);",
               "(REMOVAL (posedge RN) (posedge CK) (7))");
  EXPECT_EQ(tc.limit, 7u);
  EXPECT_TRUE(warnings.empty());
}

TEST_F(SdfReferenceFirstCheck, RecremReadsItsFirstSignalAsTheReference) {
  const TimingCheckEntry& tc =
      Annotate("$recrem(posedge RN, posedge CK, 3, 4, n);",
               "(RECREM (posedge RN) (posedge CK) (1) (2))");
  EXPECT_EQ(tc.limit, 1u);
  EXPECT_EQ(tc.limit2, 2u);
  EXPECT_TRUE(warnings.empty());
}

TEST_F(SdfReferenceFirstCheck, SkewReadsItsFirstSignalAsTheReference) {
  const TimingCheckEntry& tc =
      Annotate("$skew(posedge CK, posedge CK2, 3, n);",
               "(SKEW (posedge CK) (posedge CK2) (7))");
  EXPECT_EQ(tc.limit, 7u);
  EXPECT_TRUE(warnings.empty());
}

TEST_F(SdfReferenceFirstCheck, BidirectskewReadsItsFirstSignalAsTheReference) {
  const TimingCheckEntry& tc =
      Annotate("$fullskew(posedge CK, posedge CK2, 3, 4, n);",
               "(BIDIRECTSKEW (posedge CK) (posedge CK2) (1) (2))");
  EXPECT_EQ(tc.limit, 1u);
  EXPECT_EQ(tc.limit2, 2u);
  EXPECT_TRUE(warnings.empty());
}

TEST_F(SdfReferenceFirstCheck, NochangeReadsItsFirstSignalAsTheReference) {
  const TimingCheckEntry& tc = Annotate("$nochange(posedge CK, D, 3, 4, n);",
                                        "(NOCHANGE (posedge CK) D (1) (2))");
  EXPECT_EQ(tc.start_edge_offset, 1);
  EXPECT_EQ(tc.end_edge_offset, 2);
  EXPECT_TRUE(warnings.empty());
}

}  // namespace
