#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "fixture_specify_manager.h"
#include "parser/ast_specify.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_sdf.h"

using namespace delta;

namespace {

bool BuildSpecifyFromSource(const std::string& src, SimFixture& f,
                            SpecifyManager& mgr) {
  auto* cu = RunModuleSource(src, f);
  if (cu == nullptr) return false;
  for (auto* mod : cu->modules) {
    RegisterPathDelays(*mod, f, mgr);
    RegisterTimingChecks(*mod, f, mgr);
    RegisterSpecparamValues(*mod, f, mgr);
  }
  return true;
}

const char* const kDesign =
    "module t(input a, input b, input clk, input d, output y, output z);\n"
    "  reg ntf;\n"
    "  specify\n"
    "    specparam tRise = 11;\n"
    "    (a => y) = 21;\n"
    "    (b => z) = 31;\n"
    "    $setup(d, posedge clk, 41, ntf);\n"
    "    $hold(posedge clk, d, 51, ntf);\n"
    "  endspecify\n"
    "endmodule\n";

uint64_t LimitOf(const SpecifyManager& mgr, TimingCheckKind kind) {
  for (const auto& tc : mgr.GetTimingChecks()) {
    if (tc.kind == kind) return tc.limit;
  }
  return ~0ull;
}

uint64_t SpecparamOf(const SpecifyManager& mgr, const std::string& name) {
  for (const auto& sp : mgr.GetSpecparamValues()) {
    if (sp.name == name) return sp.value;
  }
  return ~0ull;
}

TimingCheckEntry CheckOfKind(const SpecifyManager& mgr, TimingCheckKind kind) {
  for (const auto& tc : mgr.GetTimingChecks()) {
    if (tc.kind == kind) return tc;
  }
  return TimingCheckEntry{};
}

PathDelay PathBetween(const SpecifyManager& mgr, std::string_view src,
                      std::string_view dst) {
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == src && pd.dst_port == dst) return pd;
  }
  return PathDelay{};
}

SdfAnnotationResult AnnotateFileOnto(const std::string& sdf,
                                     SpecifyManager& mgr) {
  SdfFile file;
  EXPECT_TRUE(ParseSdf(sdf, file));
  return AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);
}

SdfAnnotationResult AnnotateOntoDesign(const std::string& sdf, SimFixture& f,
                                       SpecifyManager& mgr) {
  EXPECT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));
  return AnnotateFileOnto(sdf, mgr);
}

TEST(SdfAnnotator, EachUnannotatableConstructProducesItsOwnWarning) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (DEVICE u1 (10) (20))
            (DEVICE u2 (30) (40))
          )
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SpecifyManager mgr;
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_EQ(result.warnings.size(), 2u);
}

TEST(SdfAnnotator, CondWrappingNonIopathWarns) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (COND mode (INTERCONNECT u1.q u2.d (10) (20)))
          )
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SpecifyManager mgr;
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("COND"), std::string::npos);
  EXPECT_TRUE(mgr.GetInterconnectDelays().empty());
}

TEST(SdfAnnotator, CondElseWrappingNonIopathWarns) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (CONDELSE (INTERCONNECT u1.q u2.d (10) (20)))
          )
        )
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SpecifyManager mgr;
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("CONDELSE"), std::string::npos);
  EXPECT_TRUE(mgr.GetInterconnectDelays().empty());
}

TEST(SdfAnnotator, LabelWithUnknownModeWarnsAndWritesNoSpecparam) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (LABEL (SOMEMODE (tRise 77)))
      )
    )
  )",
                                   f, mgr);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("LABEL"), std::string::npos);
  EXPECT_EQ(SpecparamOf(mgr, "tRise"), 11u);
  EXPECT_EQ(mgr.GetSpecparamValues().size(), 1u);
}

TEST(SdfAnnotator, UnknownTimingCheckKeywordWarnsAndLeavesCheckAlone) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (TIMINGCHECK (NOSUCHCHECK d (posedge clk) (5)))
      )
    )
  )",
                                   f, mgr);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("NOSUCHCHECK"), std::string::npos);
  ASSERT_EQ(mgr.TimingCheckCount(), 2u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kSetup), 41u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kHold), 51u);
}

TEST(SdfAnnotator, TimingCheckMatchingNoDeclarationWarns) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (TIMINGCHECK (SETUP b (posedge a) (5)))
      )
    )
  )",
                                   f, mgr);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("SETUP"), std::string::npos);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kSetup), 41u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kHold), 51u);
}

TEST(SdfAnnotator, IopathMatchingNoDeclaredPathWarnsAndAddsNoPath) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(
      "(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1)"
      " (DELAY (ABSOLUTE (IOPATH a z (5))))))",
      f, mgr);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("IOPATH"), std::string::npos);
  EXPECT_EQ(mgr.GetPathDelays().size(), 2u);
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 21u);
}

TEST(SdfAnnotator, ConditionalIopathMatchingNoDeclaredPathWarns) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(
      "(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1)"
      " (DELAY (ABSOLUTE (COND en (IOPATH a y (5)))))))",
      f, mgr);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("IOPATH"), std::string::npos);
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 21u);
}

TEST(SdfAnnotator, PathpulseMatchingNoDeclaredPathWarns) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(
      "(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1)"
      " (DELAY (ABSOLUTE (PATHPULSE a z (1) (2))))))",
      f, mgr);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("PATHPULSE"), std::string::npos);
}

TEST(SdfAnnotator, LabelNamingNoSpecparamWarns) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(
      "(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1)"
      " (LABEL (ABSOLUTE (tFall 9)))))",
      f, mgr);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("tFall"), std::string::npos);
  EXPECT_EQ(SpecparamOf(mgr, "tRise"), 11u);
}

TEST(SdfAnnotator, CheckCarryingScondWarnsAndTheNextCheckLands) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(
      "(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1) (TIMINGCHECK"
      " (SETUPHOLD d (posedge clk) (1) (2) (SCOND en))"
      " (SETUP d (posedge clk) (5)))))",
      f, mgr);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("SCOND"), std::string::npos);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kSetup), 5u);
}

TEST(SdfAnnotator, TripleLeavingOutTheSelectedMemberLeavesTheValue) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(
      "(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1)"
      " (DELAY (ABSOLUTE (IOPATH a y (1::3)) (IOPATH b z (9))))))",
      f, mgr);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 21u);
  EXPECT_EQ(mgr.GetPathDelay("b", "z"), 9u);
}

TEST(SdfAnnotator, TripleLeavingOutMinimumOrMaximumLeavesTheValue) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));
  SdfFile min_file;
  ASSERT_TRUE(
      ParseSdf("(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1)"
               " (DELAY (ABSOLUTE (IOPATH a y (:2:3))))))",
               min_file));
  AnnotateSdfToManager(min_file, mgr, SdfMtm::kMinimum);
  SdfFile max_file;
  ASSERT_TRUE(
      ParseSdf("(DELAYFILE (CELL (CELLTYPE \"t\") (INSTANCE u1)"
               " (DELAY (ABSOLUTE (IOPATH b z (1:2:))))))",
               max_file));
  AnnotateSdfToManager(max_file, mgr, SdfMtm::kMaximum);

  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 21u);
  EXPECT_EQ(mgr.GetPathDelay("b", "z"), 31u);
}

TEST(SdfAnnotator, UnknownDelaySectionModeWarnsAndAnnotatesNothing) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (DELAY (SOMEMODE (IOPATH a y (7) (7))))
      )
    )
  )",
                                   f, mgr);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("SOMEMODE"), std::string::npos);
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 21u);
}

TEST(SdfAnnotator, IopathRetainSubSpecIsIgnoredWhileItsDelaysAnnotate) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (RETAIN (3) (4)) (7) (7))))
      )
    )
  )",
                                   f, mgr);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 7u);
  EXPECT_EQ(mgr.GetPathDelay("b", "z"), 31u);
}

TEST(SdfAnnotator, FullySupportedFileWarnsNothing) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (IOPATH a y (7) (7))
            (INTERCONNECT u1.q u2.d (2) (3))
          )
        )
        (TIMINGCHECK (SETUP d (posedge clk) (5)))
        (LABEL (ABSOLUTE (tRise 9)))
      )
    )
  )",
                                   f, mgr);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 7u);
  EXPECT_EQ(SpecparamOf(mgr, "tRise"), 9u);
  ASSERT_EQ(mgr.TimingCheckCount(), 2u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kSetup), 5u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kHold), 51u);
  EXPECT_EQ(mgr.GetInterconnectDelays().size(), 1u);
}

TEST(SdfAnnotator, TimingenvIsIgnoredWithoutWarnings) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (TIMINGENV
        (PATHCONSTRAINT a b (10))
      )
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (10) (20))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 10u);
}

TEST(SdfAnnotator, TimingenvInsideCellIsIgnoredWithoutWarnings) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (TIMINGENV
          (PATHCONSTRAINT a b (10))
        )
        (DELAY (ABSOLUTE (IOPATH a y (10) (20))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 10u);
}

TEST(SdfAnnotator, HeaderConstructsAreIgnoredWithoutWarnings) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (SDFVERSION "3.0")
      (DESIGN "t")
      (DATE "Tuesday")
      (VENDOR "acme")
      (PROGRAM "delaycalc")
      (VERSION "1.2")
      (DIVIDER .)
      (VOLTAGE 1.8:1.8:1.8)
      (PROCESS "typical")
      (TEMPERATURE 25:25:25)
      (TIMESCALE 1ns)
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (10) (20))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(file.version, "3.0");
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 10u);
}

TEST(SdfAnnotator, PartialSdfLeavesUnmentionedDeclaredValuesUnchanged) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (7) (7))))
      )
    )
  )",
                                   f, mgr);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 7u);
  EXPECT_EQ(mgr.GetPathDelay("b", "z"), 31u);
  EXPECT_EQ(SpecparamOf(mgr, "tRise"), 11u);
  ASSERT_EQ(mgr.TimingCheckCount(), 2u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kSetup), 41u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kHold), 51u);
}

TEST(SdfAnnotator, ValuelessSdfLeavesEveryDeclaredValueUnchanged) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (SDFVERSION "3.0")
      (DESIGN "t")
      (TIMINGENV
        (PATHCONSTRAINT a b (10))
      )
    )
  )",
                                   f, mgr);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 21u);
  EXPECT_EQ(mgr.GetPathDelay("b", "z"), 31u);
  EXPECT_EQ(SpecparamOf(mgr, "tRise"), 11u);
  ASSERT_EQ(mgr.TimingCheckCount(), 2u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kSetup), 41u);
  EXPECT_EQ(LimitOf(mgr, TimingCheckKind::kHold), 51u);
}

TEST(SdfAnnotator, EmptySdfPreservesInterconnectDelay) {
  SpecifyManager mgr;
  InterconnectDelay ic;
  ic.src_port = "u1.q";
  ic.dst_port = "u2.d";
  ic.rise = 7;
  ic.fall = 9;
  mgr.AddInterconnectDelay(ic);

  SdfFile empty_file;
  SdfAnnotationResult result =
      AnnotateSdfToManager(empty_file, mgr, SdfMtm::kTypical);

  EXPECT_TRUE(result.warnings.empty());
  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  EXPECT_EQ(mgr.GetInterconnectDelays()[0].rise, 7u);
  EXPECT_EQ(mgr.GetInterconnectDelays()[0].fall, 9u);
}

TEST(SdfAnnotator, UnmentionedMultiValuePathKeepsEveryTransitionSlot) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(
      BuildSpecifyFromSource("module t(input a, input b, output y, output z);\n"
                             "  specify\n"
                             "    (a => y) = 21;\n"
                             "    (b => z) = (1, 2, 3, 4, 5, 6);\n"
                             "  endspecify\n"
                             "endmodule\n",
                             f, mgr));
  const PathDelay kBefore = PathBetween(mgr, "b", "z");
  ASSERT_EQ(kBefore.delay_count, 6u);
  ASSERT_NE(kBefore.delays[11], 0u);

  auto result = AnnotateFileOnto(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (7) (7))))
      )
    )
  )",
                                 mgr);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 7u);
  const PathDelay kAfter = PathBetween(mgr, "b", "z");
  EXPECT_EQ(kAfter.delay_count, kBefore.delay_count);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(kAfter.delays[i], kBefore.delays[i]) << "transition slot " << i;
  }
}

TEST(SdfAnnotator, UnmentionedSetupholdKeepsBothLimits) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(
      "module t(input a, input clk, input d, output y);\n"
      "  reg ntf;\n"
      "  specify\n"
      "    (a => y) = 21;\n"
      "    $setuphold(posedge clk, d, 12, 22, ntf);\n"
      "  endspecify\n"
      "endmodule\n",
      f, mgr));
  const TimingCheckEntry kBefore =
      CheckOfKind(mgr, TimingCheckKind::kSetuphold);
  ASSERT_EQ(kBefore.limit, 12u);
  ASSERT_EQ(kBefore.limit2, 22u);

  auto result = AnnotateFileOnto(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (7) (7))))
      )
    )
  )",
                                 mgr);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 7u);
  const TimingCheckEntry kAfter = CheckOfKind(mgr, TimingCheckKind::kSetuphold);
  EXPECT_EQ(kAfter.limit, 12u);
  EXPECT_EQ(kAfter.limit2, 22u);
}

TEST(SdfAnnotator, PathDelayTakenFromSpecparamIsPreserved) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(
      BuildSpecifyFromSource("module t(input a, input b, output y, output z);\n"
                             "  specify\n"
                             "    specparam tRise = 13;\n"
                             "    (a => y) = tRise;\n"
                             "    (b => z) = 31;\n"
                             "  endspecify\n"
                             "endmodule\n",
                             f, mgr));
  ASSERT_EQ(mgr.GetPathDelay("a", "y"), 13u);

  auto result = AnnotateFileOnto(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH b z (7) (7))))
      )
    )
  )",
                                 mgr);

  EXPECT_TRUE(result.warnings.empty());
  EXPECT_EQ(mgr.GetPathDelay("b", "z"), 7u);
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 13u);
  EXPECT_EQ(SpecparamOf(mgr, "tRise"), 13u);
}

TEST(SdfAnnotator, UnmentionedInterconnectSurvivesWhileSiblingIsAnnotated) {
  SpecifyManager mgr;
  InterconnectDelay named;
  named.src_port = "u1.q";
  named.dst_port = "u2.d";
  named.rise = 7;
  named.fall = 9;
  mgr.AddInterconnectDelay(named);

  InterconnectDelay untouched;
  untouched.src_port = "u3.q";
  untouched.dst_port = "u4.d";
  untouched.rise = 41;
  untouched.fall = 43;
  mgr.AddInterconnectDelay(untouched);

  auto result = AnnotateFileOnto(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (INTERCONNECT u1.q u2.d (2) (3))))
      )
    )
  )",
                                 mgr);

  EXPECT_TRUE(result.warnings.empty());
  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 2u);
  for (const auto& ic : mgr.GetInterconnectDelays()) {
    if (ic.src_port == "u1.q") {
      EXPECT_EQ(ic.rise, 2u);
      EXPECT_EQ(ic.fall, 3u);
    } else {
      EXPECT_EQ(ic.rise, 41u);
      EXPECT_EQ(ic.fall, 43u);
    }
  }
}

TEST(SdfAnnotator, UnannotatableConstructInLaterCellStillWarns) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH a y (10) (20))))
      )
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u2)
        (DELAY (ABSOLUTE (DEVICE u2 (30) (40))))
      )
    )
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));

  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kDesign, f, mgr));
  SdfAnnotationResult result =
      AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(result.warnings.size(), 1u);
  EXPECT_NE(result.warnings[0].find("DEVICE"), std::string::npos);
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 10u);
}

TEST(SdfAnnotator, SilentIgnoredWarnedAndAnnotatedAllCoexist) {
  SimFixture f;
  SpecifyManager mgr;
  auto result = AnnotateOntoDesign(R"(
    (DELAYFILE
      (TIMINGENV
        (PATHCONSTRAINT a b (5))
      )
      (CELL
        (CELLTYPE "t")
        (INSTANCE u1)
        (DELAY
          (ABSOLUTE
            (DEVICE u1 (3) (5))
            (IOPATH a y (1) (2))
          )
        )
      )
    )
  )",
                                   f, mgr);

  EXPECT_EQ(result.warnings.size(), 1u);
  EXPECT_EQ(mgr.GetPathDelay("a", "y"), 1u);
  EXPECT_EQ(mgr.GetPathDelay("b", "z"), 31u);
}

}  // namespace
