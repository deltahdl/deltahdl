#include <gtest/gtest.h>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

TEST(SdfParser, SdfIopathEntry) {
  SdfIopath entry;
  entry.src_port = "a";
  entry.dst_port = "y";
  entry.rise.typ_val = 100;
  entry.fall.typ_val = 200;
  EXPECT_EQ(entry.src_port, "a");
  EXPECT_EQ(entry.rise.typ_val, 100u);
  EXPECT_EQ(entry.fall.typ_val, 200u);
}

TEST(SdfParser, SdfTimingCheckEntry) {
  SdfTimingCheck tc;
  tc.check_type = SdfCheckType::kSetup;
  tc.ref_port = "clk";
  tc.data_port = "d";
  tc.limit.typ_val = 50;
  EXPECT_EQ(tc.ref_port, "clk");
  EXPECT_EQ(tc.limit.typ_val, 50u);
}

TEST(SdfParser, SdfCellDefault) {
  SdfCell cell;
  EXPECT_TRUE(cell.cell_type.empty());
  EXPECT_TRUE(cell.instance.empty());
  EXPECT_TRUE(cell.iopaths.empty());
  EXPECT_TRUE(cell.timing_checks.empty());
}

TEST(SdfParser, ParseCellWithIopath) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (IOPATH a y (10) (20))
          )
        )
      )
    )
  )";
  bool ok = ParseSdf(sdf, file);
  EXPECT_TRUE(ok);
  ASSERT_EQ(file.cells.size(), 1u);
  EXPECT_EQ(file.cells[0].cell_type, "buf");
  EXPECT_EQ(file.cells[0].instance, "u1");
  ASSERT_EQ(file.cells[0].iopaths.size(), 1u);
}

TEST(SdfParser, ParseCellWithIopath_Ports) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (IOPATH a y (10) (20))
          )
        )
      )
    )
  )";
  ParseSdf(sdf, file);
  EXPECT_EQ(file.cells[0].iopaths[0].src_port, "a");
  EXPECT_EQ(file.cells[0].iopaths[0].dst_port, "y");
  EXPECT_EQ(file.cells[0].iopaths[0].rise.typ_val, 10u);
  EXPECT_EQ(file.cells[0].iopaths[0].fall.typ_val, 20u);
}

TEST(SdfParser, ParseTimingCheck) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "dff")
        (INSTANCE u2)
        (TIMINGCHECK
          (SETUP d (posedge clk) (5))
        )
      )
    )
  )";
  bool ok = ParseSdf(sdf, file);
  EXPECT_TRUE(ok);
  ASSERT_EQ(file.cells.size(), 1u);
  ASSERT_EQ(file.cells[0].timing_checks.size(), 1u);
}

TEST(SdfParser, ParseTimingCheck_Fields) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "dff")
        (INSTANCE u2)
        (TIMINGCHECK
          (SETUP d (posedge clk) (5))
        )
      )
    )
  )";
  ParseSdf(sdf, file);
  auto& tc = file.cells[0].timing_checks[0];
  EXPECT_EQ(tc.check_type, SdfCheckType::kSetup);
  EXPECT_EQ(tc.data_port, "d");
  EXPECT_EQ(tc.ref_port, "clk");
  EXPECT_EQ(tc.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.limit.typ_val, 5u);
}

TEST(SdfParser, ParseIncrementMode) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u4)
        (DELAY
          (INCREMENT
            (IOPATH a y (5) (10))
          )
        )
      )
    )
  )";
  bool ok = ParseSdf(sdf, file);
  EXPECT_TRUE(ok);
  ASSERT_EQ(file.cells[0].iopaths.size(), 1u);
  EXPECT_TRUE(file.cells[0].iopaths[0].is_increment);
}

TEST(SdfParser, ParseHoldCheck) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "dff")
        (INSTANCE u5)
        (TIMINGCHECK
          (HOLD d (posedge clk) (3))
        )
      )
    )
  )";
  bool ok = ParseSdf(sdf, file);
  EXPECT_TRUE(ok);
  auto& tc = file.cells[0].timing_checks[0];
  EXPECT_EQ(tc.check_type, SdfCheckType::kHold);
  EXPECT_EQ(tc.limit.typ_val, 3u);
}

TEST(SdfParser, ParseMultipleCells) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (10) (20))))
      )
      (CELL
        (CELLTYPE "inv")
        (INSTANCE u2)
        (DELAY (ABSOLUTE (IOPATH a y (5) (8))))
      )
    )
  )";
  bool ok = ParseSdf(sdf, file);
  EXPECT_TRUE(ok);
  EXPECT_EQ(file.cells.size(), 2u);
  EXPECT_EQ(file.cells[0].instance, "u1");
  EXPECT_EQ(file.cells[1].instance, "u2");
}

TEST(SdfParser, ParseMinTypMaxDelay) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "inv")
        (INSTANCE u3)
        (DELAY
          (ABSOLUTE
            (IOPATH a y (1:2:3) (4:5:6))
          )
        )
      )
    )
  )";
  bool ok = ParseSdf(sdf, file);
  EXPECT_TRUE(ok);
  ASSERT_EQ(file.cells[0].iopaths.size(), 1u);
}

TEST(SdfParser, ParseMinTypMaxDelay_RiseValues) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "inv")
        (INSTANCE u3)
        (DELAY
          (ABSOLUTE
            (IOPATH a y (1:2:3) (4:5:6))
          )
        )
      )
    )
  )";
  ParseSdf(sdf, file);
  auto& io = file.cells[0].iopaths[0];
  EXPECT_EQ(io.rise.min_val, 1u);
  EXPECT_EQ(io.rise.typ_val, 2u);
  EXPECT_EQ(io.rise.max_val, 3u);
}

TEST(SdfParser, ParseMinTypMaxDelay_FallValues) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "inv")
        (INSTANCE u3)
        (DELAY
          (ABSOLUTE
            (IOPATH a y (1:2:3) (4:5:6))
          )
        )
      )
    )
  )";
  ParseSdf(sdf, file);
  auto& io = file.cells[0].iopaths[0];
  EXPECT_EQ(io.fall.min_val, 4u);
  EXPECT_EQ(io.fall.typ_val, 5u);
  EXPECT_EQ(io.fall.max_val, 6u);
}

// =============================================================================
// §32.4 (parent text only) — Mapping of SDF constructs to SystemVerilog
// =============================================================================

// §32.4 sentence 1: "SDF timing values appear within a CELL declaration,
// which can contain one or more of DELAY, TIMINGCHECK, and LABEL sections."
// All three sections must coexist in a single CELL without the parser
// rejecting the file or losing the surrounding metadata.
TEST(SdfConstructMapping, CellWithAllThreeSectionsParses) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "dff")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (10) (20))))
        (TIMINGCHECK (SETUP d (posedge clk) (5)))
        (LABEL (ABSOLUTE (dhigh 60) (dlow 40)))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells.size(), 1u);
  EXPECT_EQ(file.cells[0].cell_type, "dff");
  EXPECT_EQ(file.cells[0].instance, "u1");
  ASSERT_EQ(file.cells[0].iopaths.size(), 1u);
  ASSERT_EQ(file.cells[0].timing_checks.size(), 1u);
}

// §32.4 sentence 1 ("one or more of"): a CELL with only LABEL — no DELAY
// or TIMINGCHECK — must parse. The LRM does not require any particular
// section to be present, only that one of the three is.
TEST(SdfConstructMapping, CellWithOnlyLabelSectionParses) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "clk_gen")
        (INSTANCE u2)
        (LABEL (ABSOLUTE (dhigh 60)))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells.size(), 1u);
  EXPECT_EQ(file.cells[0].cell_type, "clk_gen");
  EXPECT_EQ(file.cells[0].instance, "u2");
}

// §32.4 sentence 5: "Backannotation into SystemVerilog is done by matching
// SDF constructs to the corresponding SystemVerilog declarations and then
// replacing the existing SystemVerilog timing values with those from the
// SDF file." Annotating the same SDF file twice must converge — the second
// pass replaces the first pass's specparam value rather than producing a
// second entry for the same name.
TEST(SdfConstructMapping, ReannotationReplacesSpecparamRatherThanDuplicating) {
  SdfFile file;
  SdfCell cell;
  SdfSpecparam sp;
  sp.name = "tHold";
  sp.value.typ_val = 11;
  cell.specparams.push_back(sp);
  file.cells.push_back(cell);

  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetSpecparamValues().size(), 1u);
  EXPECT_EQ(mgr.GetSpecparamValues()[0].name, "tHold");
  EXPECT_EQ(mgr.GetSpecparamValues()[0].value, 11u);
}

// §32.4 sentence 5 (the "replacing" half): when a second annotation pass
// supplies a different value for an already-named declaration, the new
// value must take effect. The same-value convergence test above can be
// satisfied by a first-write-wins implementation; this companion pins down
// that the second pass actually overwrites the prior value.
TEST(SdfConstructMapping, ReannotationOverwritesPriorSpecparamValue) {
  SpecifyManager mgr;

  SdfFile first;
  {
    SdfCell cell;
    SdfSpecparam sp;
    sp.name = "tHold";
    sp.value.typ_val = 11;
    cell.specparams.push_back(sp);
    first.cells.push_back(cell);
  }
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  {
    SdfCell cell;
    SdfSpecparam sp;
    sp.name = "tHold";
    sp.value.typ_val = 47;
    cell.specparams.push_back(sp);
    second.cells.push_back(cell);
  }
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetSpecparamValues().size(), 1u);
  EXPECT_EQ(mgr.GetSpecparamValues()[0].value, 47u);
}

}  // namespace
