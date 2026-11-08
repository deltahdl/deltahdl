#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "fixture_sdf_design.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_sdf.h"

using namespace delta;

namespace {

struct Design : SdfDesign {
  bool Build(const std::string& src) {
    if (!SdfDesign::Lower(src)) return false;
    mgr.BindDesignInterconnect(CollectInterconnectTopology(*cu, Top()));
    return true;
  }

  SdfAnnotationResult Annotate(const std::string& sdf,
                               SdfMtm mtm = SdfMtm::kTypical) {
    SdfFile file;
    EXPECT_TRUE(ParseSdf(sdf, file));
    return AnnotateSdfToManager(file, mgr, mtm);
  }

  const InterconnectDelay* Load(std::string_view load) const {
    for (const auto& ic : mgr.GetInterconnectDelays()) {
      if (ic.dst_port == load) return &ic;
    }
    return nullptr;
  }

  bool AnyWarningMentions(const SdfAnnotationResult& result,
                          std::string_view text) const {
    for (const auto& w : result.warnings) {
      if (w.find(text) != std::string::npos) return true;
    }
    return false;
  }
};

std::string SdfDelay(const std::string& body, const std::string& version = {}) {
  std::string out = "(DELAYFILE ";
  if (!version.empty()) out += "(SDFVERSION \"" + version + "\") ";
  out += "(CELL (CELLTYPE \"top\") (INSTANCE top) (DELAY (ABSOLUTE " + body +
         "))))";
  return out;
}

const char* const kPairSrc =
    "module drv(q);\n"
    "  output q;\n"
    "  reg q;\n"
    "  initial begin q = 1'b0; #5 q = 1'b1; #5 q = 1'b0; end\n"
    "endmodule\n"
    "module ld(d);\n"
    "  input d;\n"
    "  wire d;\n"
    "endmodule\n"
    "module top;\n"
    "  wire n;\n"
    "  drv u1(.q(n));\n"
    "  ld u2(.d(n));\n"
    "endmodule\n";

const char* const kMultisourceSrc =
    "module drv(q);\n"
    "  output q;\n"
    "  reg q;\n"
    "endmodule\n"
    "module ld(d);\n"
    "  input d;\n"
    "  wire d;\n"
    "endmodule\n"
    "module top;\n"
    "  wire n;\n"
    "  drv s1(.q(n));\n"
    "  drv s2(.q(n));\n"
    "  ld l1(.d(n));\n"
    "  ld l2(.d(n));\n"
    "endmodule\n";

const char* const kDeepSrc =
    "module core_src(q);\n"
    "  output q;\n"
    "  reg q;\n"
    "endmodule\n"
    "module src_l2(q);\n"
    "  output q;\n"
    "  wire q;\n"
    "  core_src a(.q(q));\n"
    "endmodule\n"
    "module src_l1(q);\n"
    "  output q;\n"
    "  wire q;\n"
    "  src_l2 b(.q(q));\n"
    "endmodule\n"
    "module core_ld(d);\n"
    "  input d;\n"
    "  wire d;\n"
    "endmodule\n"
    "module ld_l2(d);\n"
    "  input d;\n"
    "  wire d;\n"
    "  core_ld m1(.d(d));\n"
    "endmodule\n"
    "module ld_l1(d);\n"
    "  input d;\n"
    "  wire d;\n"
    "  ld_l2 m2(.d(d));\n"
    "endmodule\n"
    "module top;\n"
    "  wire n;\n"
    "  src_l1 u1(.q(n));\n"
    "  ld_l1 u2(.d(n));\n"
    "endmodule\n";

const char* const kInoutSrc =
    "module drv(q);\n"
    "  output q;\n"
    "  reg q;\n"
    "endmodule\n"
    "module bidir(io);\n"
    "  inout io;\n"
    "  wire io;\n"
    "endmodule\n"
    "module ld(d);\n"
    "  input d;\n"
    "  wire d;\n"
    "endmodule\n"
    "module top;\n"
    "  wire n;\n"
    "  drv u1(.q(n));\n"
    "  bidir u2(.io(n));\n"
    "  ld u3(.d(n));\n"
    "endmodule\n";

const char* const kOtherNetMultisourceSrc =
    "module drv(q);\n"
    "  output q;\n"
    "  reg q;\n"
    "endmodule\n"
    "module ld(d);\n"
    "  input d;\n"
    "  wire d;\n"
    "endmodule\n"
    "module top;\n"
    "  wire na;\n"
    "  wire nb;\n"
    "  drv x1(.q(na));\n"
    "  drv s1(.q(nb));\n"
    "  drv s2(.q(nb));\n"
    "  ld l1(.d(nb));\n"
    "endmodule\n";

TEST(SdfInterconnectAnnotation,
     ParseInterconnectConstructCarriesSourceAndLoad) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (INTERCONNECT u2.q u3.d (4) (9))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells.size(), 1u);
  ASSERT_EQ(file.cells[0].interconnects.size(), 1u);
  const auto& ic = file.cells[0].interconnects[0];
  EXPECT_EQ(ic.kind, SdfInterconnectKind::kInterconnect);
  EXPECT_EQ(ic.src_port, "u2.q");
  EXPECT_EQ(ic.dst_port, "u3.d");
  EXPECT_EQ(ic.rise.typ_val, 4u);
  EXPECT_EQ(ic.fall.typ_val, 9u);
}

TEST(SdfInterconnectAnnotation, ParsePortConstructHasEmptySourceAndKindPort) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (PORT u3.d (5) (8))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells[0].interconnects.size(), 1u);
  const auto& ic = file.cells[0].interconnects[0];
  EXPECT_EQ(ic.kind, SdfInterconnectKind::kPort);
  EXPECT_TRUE(ic.src_port.empty());
  EXPECT_EQ(ic.dst_port, "u3.d");
  EXPECT_EQ(ic.rise.typ_val, 5u);
  EXPECT_EQ(ic.fall.typ_val, 8u);
}

TEST(SdfInterconnectAnnotation,
     ParseNetdelayConstructHasEmptySourceAndKindNetdelay) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (NETDELAY u3.d (6) (12))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells[0].interconnects.size(), 1u);
  const auto& ic = file.cells[0].interconnects[0];
  EXPECT_EQ(ic.kind, SdfInterconnectKind::kNetdelay);
  EXPECT_TRUE(ic.src_port.empty());
  EXPECT_EQ(ic.dst_port, "u3.d");
  EXPECT_EQ(ic.rise.typ_val, 6u);
  EXPECT_EQ(ic.fall.typ_val, 12u);
}

TEST(SdfInterconnectAnnotation, NetdelayIsAnnotatedForAVersionThatDefinesIt) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(NETDELAY u2/d (4))", "2.1"));
  EXPECT_FALSE(d.AnyWarningMentions(result, "NETDELAY"));
  ASSERT_NE(d.Load("u2/d"), nullptr);
  EXPECT_EQ(d.Load("u2/d")->delays[0], 4u);
}

TEST(SdfInterconnectAnnotation, NetdelayIsAnnotatedForTheIeeeSdfVersion) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(NETDELAY u2/d (4))", "4.0"));
  EXPECT_FALSE(d.AnyWarningMentions(result, "NETDELAY"));
  ASSERT_NE(d.Load("u2/d"), nullptr);
  EXPECT_EQ(d.Load("u2/d")->delays[0], 4u);
}

TEST(SdfInterconnectAnnotation, NetdelayIsAnnotatedWhenNoVersionIsDeclared) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(NETDELAY u2/d (4))"));
  EXPECT_FALSE(d.AnyWarningMentions(result, "NETDELAY"));
  ASSERT_NE(d.Load("u2/d"), nullptr);
  EXPECT_EQ(d.Load("u2/d")->delays[0], 4u);
}

TEST(SdfInterconnectAnnotation, NetdelayIsRefusedForAVersionWithoutIt) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(NETDELAY u2/d (4))", "3.0"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "NETDELAY"));
  EXPECT_EQ(d.Load("u2/d"), nullptr);
}

const char* const kGateSrc =
    "module ld(d);\n"
    "  input d;\n"
    "  wire d;\n"
    "endmodule\n"
    "module top;\n"
    "  wire a;\n"
    "  wire n;\n"
    "  and g1(n, a, a);\n"
    "  ld u2(.d(n));\n"
    "endmodule\n";

TEST(SdfInterconnectAnnotation, PrimitivePinSourceIsRefused) {
  Design d;
  ASSERT_TRUE(d.Build(kGateSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT g1/out u2/d (4))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "primitive pin"));
  EXPECT_EQ(d.Load("u2/d"), nullptr);
}

TEST(SdfInterconnectAnnotation, PrimitivePinLoadIsRefused) {
  Design d;
  ASSERT_TRUE(d.Build(kGateSrc));
  auto result = d.Annotate(SdfDelay("(PORT g1/in (4))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "primitive pin"));
  EXPECT_TRUE(d.mgr.GetInterconnectDelays().empty());
}

const char* const kUdpSrc =
    "primitive udp_buf(out, in);\n"
    "  output out;\n"
    "  input in;\n"
    "  table\n"
    "    0 : 0;\n"
    "    1 : 1;\n"
    "  endtable\n"
    "endprimitive\n"
    "module ld(d);\n"
    "  input d;\n"
    "  wire d;\n"
    "endmodule\n"
    "module top;\n"
    "  wire a;\n"
    "  wire n;\n"
    "  udp_buf ud1(n, a);\n"
    "  ld u2(.d(n));\n"
    "endmodule\n";

TEST(SdfInterconnectAnnotation, UdpPinSourceIsRefused) {
  Design d;
  ASSERT_TRUE(d.Build(kUdpSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT ud1/out u2/d (4))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "primitive pin"));
  EXPECT_EQ(d.Load("u2/d"), nullptr);
}

TEST(SdfInterconnectAnnotation, PortConstructAnnotatesTheNamedPort) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(PORT u2/d (3) (6))"));
  EXPECT_TRUE(result.warnings.empty());
  const auto* got = d.Load("u2/d");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 3u);
  EXPECT_EQ(got->delays[1], 6u);
}

TEST(SdfInterconnectAnnotation, PortDelayIsTheDelayFromEverySourceOnTheNet) {
  Design d;
  ASSERT_TRUE(d.Build(kMultisourceSrc));
  d.Annotate(SdfDelay("(PORT l1/d (8))"));
  const auto* from_s1 = d.mgr.FindInterconnectDelay("s1/q", "l1/d");
  const auto* from_s2 = d.mgr.FindInterconnectDelay("s2/q", "l1/d");
  ASSERT_NE(from_s1, nullptr);
  ASSERT_NE(from_s2, nullptr);
  EXPECT_EQ(from_s1->delays[0], 8u);
  EXPECT_EQ(from_s2->delays[0], 8u);
}

TEST(SdfInterconnectAnnotation, PortConstructNamingNoPortIsWarnedAbout) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(PORT u9/d (3))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "names no port"));
  EXPECT_TRUE(d.mgr.GetInterconnectDelays().empty());
}

TEST(SdfInterconnectAnnotation, PortConstructNamingANetIsWarnedAbout) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(PORT n (5))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "names no port"));
  EXPECT_TRUE(d.mgr.GetInterconnectDelays().empty());
}

TEST(SdfInterconnectAnnotation, PortConstructNamingAnOutputPortIsWarnedAbout) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(PORT u1/q (3))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "not an input or inout"));
  EXPECT_TRUE(d.mgr.GetInterconnectDelays().empty());
}

TEST(SdfInterconnectAnnotation, NetdelayNamingAPortAnnotatesThatPort) {
  Design d;
  ASSERT_TRUE(d.Build(kMultisourceSrc));
  auto result = d.Annotate(SdfDelay("(NETDELAY l1/d (5))"));
  EXPECT_TRUE(result.warnings.empty());
  ASSERT_NE(d.Load("l1/d"), nullptr);
  EXPECT_EQ(d.Load("l1/d")->delays[0], 5u);
  EXPECT_EQ(d.Load("l2/d"), nullptr);
}

TEST(SdfInterconnectAnnotation, NetdelayNamingANetReachesEveryLoadPortOnIt) {
  Design d;
  ASSERT_TRUE(d.Build(kMultisourceSrc));
  auto result = d.Annotate(SdfDelay("(NETDELAY n (7))"));
  EXPECT_TRUE(result.warnings.empty());
  ASSERT_NE(d.Load("l1/d"), nullptr);
  ASSERT_NE(d.Load("l2/d"), nullptr);
  EXPECT_EQ(d.Load("l1/d")->delays[0], 7u);
  EXPECT_EQ(d.Load("l2/d")->delays[0], 7u);
}

TEST(SdfInterconnectAnnotation, NetdelayOnAMultisourceNetIsFromAllSources) {
  Design d;
  ASSERT_TRUE(d.Build(kMultisourceSrc));
  d.Annotate(SdfDelay("(NETDELAY n (7))"));
  EXPECT_NE(d.mgr.FindInterconnectDelay("s1/q", "l2/d"), nullptr);
  EXPECT_NE(d.mgr.FindInterconnectDelay("s2/q", "l2/d"), nullptr);
}

TEST(SdfInterconnectAnnotation, NetdelayToAPortWithSeveralSourcesIsFromAll) {
  Design d;
  ASSERT_TRUE(d.Build(kMultisourceSrc));
  d.Annotate(SdfDelay("(NETDELAY l1/d (5))"));
  const auto* from_s1 = d.mgr.FindInterconnectDelay("s1/q", "l1/d");
  const auto* from_s2 = d.mgr.FindInterconnectDelay("s2/q", "l1/d");
  ASSERT_NE(from_s1, nullptr);
  ASSERT_NE(from_s2, nullptr);
  EXPECT_EQ(from_s1->delays[0], 5u);
  EXPECT_EQ(from_s2->delays[0], 5u);
}

TEST(SdfInterconnectAnnotation, NetdelayToAnOutputPortIsWarnedAbout) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(NETDELAY u1/q (5))"));
  EXPECT_TRUE(d.AnyWarningMentions(
      result, "not an input or inout module port or a net"));
  EXPECT_TRUE(d.mgr.GetInterconnectDelays().empty());
}

TEST(SdfInterconnectAnnotation, NetdelayNamingNeitherPortNorNetIsWarnedAbout) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(NETDELAY nothing (5))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "neither a port nor a net"));
  EXPECT_TRUE(d.mgr.GetInterconnectDelays().empty());
}

TEST(SdfInterconnectAnnotation, InterconnectAnnotatesBetweenSourceAndLoad) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/d (3) (6))"));
  EXPECT_TRUE(result.warnings.empty());
  const auto* got = d.mgr.FindInterconnectDelay("u1/q", "u2/d");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 3u);
  EXPECT_EQ(got->delays[1], 6u);
}

TEST(SdfInterconnectAnnotation, MultisourceNetCarriesADelayPerSourceLoadPair) {
  Design d;
  ASSERT_TRUE(d.Build(kMultisourceSrc));
  d.Annotate(
      SdfDelay("(INTERCONNECT s1/q l1/d (3)) (INTERCONNECT s2/q l1/d (11))"));
  const auto* from_s1 = d.mgr.FindInterconnectDelay("s1/q", "l1/d");
  const auto* from_s2 = d.mgr.FindInterconnectDelay("s2/q", "l1/d");
  ASSERT_NE(from_s1, nullptr);
  ASSERT_NE(from_s2, nullptr);
  EXPECT_EQ(from_s1->delays[0], 3u);
  EXPECT_EQ(from_s2->delays[0], 11u);
}

TEST(SdfInterconnectAnnotation, InterconnectNamingNoLoadPortIsWarnedAbout) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT u1/q absent/d (4))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "names no load port"));
  EXPECT_TRUE(d.mgr.GetInterconnectDelays().empty());
}

TEST(SdfInterconnectAnnotation, InterconnectNamingANetReachesItsLoadPorts) {
  Design d;
  ASSERT_TRUE(d.Build(kDeepSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT u1/b/a/q n (3))"));
  EXPECT_TRUE(result.warnings.empty());
  ASSERT_NE(d.Load("u2/d"), nullptr);
  ASSERT_NE(d.Load("u2/m2/d"), nullptr);
  ASSERT_NE(d.Load("u2/m2/m1/d"), nullptr);
  EXPECT_EQ(d.Load("u2/d")->delays[0], 3u);
  EXPECT_EQ(d.Load("u2/m2/d")->delays[0], 3u);
  EXPECT_EQ(d.Load("u2/m2/m1/d")->delays[0], 3u);
}

TEST(SdfInterconnectAnnotation, MissingSourceWarnsAndStillAnnotatesTheLoad) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT u9/q u2/d (4))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "not found"));
  const auto* got = d.Load("u2/d");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 4u);
  const InterconnectDelay* found = d.mgr.FindInterconnectDelay("n", "u2/d");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->delays[0], 4u);
}

TEST(SdfInterconnectAnnotation,
     MissingSourceOnAMultisourceNetBecomesFromAllSources) {
  Design d;
  ASSERT_TRUE(d.Build(kMultisourceSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT nowhere/q l1/d (4))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "not found"));
  EXPECT_NE(d.mgr.FindInterconnectDelay("s1/q", "l1/d"), nullptr);
  EXPECT_NE(d.mgr.FindInterconnectDelay("s2/q", "l1/d"), nullptr);
}

TEST(SdfInterconnectAnnotation,
     MissingSourceOnASingleSourceNetIsFromItsOneSource) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  d.Annotate(SdfDelay("(INTERCONNECT u9/q u2/d (4))"));
  EXPECT_NE(d.mgr.FindInterconnectDelay("u1/q", "u2/d"), nullptr);
}

const char* const kTwoNetSrc =
    "module drv(q);\n"
    "  output q;\n"
    "  reg q;\n"
    "endmodule\n"
    "module ld(d);\n"
    "  input d;\n"
    "  wire d;\n"
    "endmodule\n"
    "module top;\n"
    "  wire na;\n"
    "  wire nb;\n"
    "  drv u1(.q(na));\n"
    "  drv u3(.q(nb));\n"
    "  ld u2(.d(nb));\n"
    "endmodule\n";

TEST(SdfInterconnectAnnotation, SourceOnAnotherNetWarnsAndStillAnnotates) {
  Design d;
  ASSERT_TRUE(d.Build(kTwoNetSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/d (9))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "not on the same net"));
  const auto* got = d.Load("u2/d");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 9u);
}

TEST(SdfInterconnectAnnotation, InputSourcePortIsWarnedAbout) {
  Design d;
  ASSERT_TRUE(d.Build(kMultisourceSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT l2/d l1/d (5))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "not an output or inout port"));
}

TEST(SdfInterconnectAnnotation, OutputLoadPortIsWarnedAboutAndNotAnnotated) {
  Design d;
  ASSERT_TRUE(d.Build(kMultisourceSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT s1/q s2/q (5))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "not an input or inout port"));
  EXPECT_EQ(d.Load("s2/q"), nullptr);
}

TEST(SdfInterconnectAnnotation, InoutPortIsAcceptedAsALoad) {
  Design d;
  ASSERT_TRUE(d.Build(kInoutSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/io (4))"));
  EXPECT_FALSE(d.AnyWarningMentions(result, "not an input or inout"));
  const auto* got = d.mgr.FindInterconnectDelay("u1/q", "u2/io");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 4u);
}

TEST(SdfInterconnectAnnotation, InoutPortIsAcceptedAsASource) {
  Design d;
  ASSERT_TRUE(d.Build(kInoutSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT u2/io u3/d (6))"));
  EXPECT_FALSE(d.AnyWarningMentions(result, "not an output or inout"));
  const auto* got = d.mgr.FindInterconnectDelay("u2/io", "u3/d");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 6u);
}

TEST(SdfInterconnectAnnotation, PortConstructAcceptsAnInoutPortAsItsLoad) {
  Design d;
  ASSERT_TRUE(d.Build(kInoutSrc));
  auto result = d.Annotate(SdfDelay("(PORT u2/io (8))"));
  EXPECT_TRUE(result.warnings.empty());
  ASSERT_NE(d.Load("u2/io"), nullptr);
  EXPECT_EQ(d.Load("u2/io")->delays[0], 8u);
}

TEST(SdfInterconnectAnnotation,
     SourceOnAnotherNetOfAMultisourceLoadBecomesFromAllSources) {
  Design d;
  ASSERT_TRUE(d.Build(kOtherNetMultisourceSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT x1/q l1/d (9))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "not on the same net"));
  const auto* from_s1 = d.mgr.FindInterconnectDelay("s1/q", "l1/d");
  const auto* from_s2 = d.mgr.FindInterconnectDelay("s2/q", "l1/d");
  ASSERT_NE(from_s1, nullptr);
  ASSERT_NE(from_s2, nullptr);
  EXPECT_EQ(from_s1->delays[0], 9u);
  EXPECT_EQ(from_s2->delays[0], 9u);
}

TEST(SdfInterconnectAnnotation, AnnotationReachesConnectedPortsBelowTheLoad) {
  Design d;
  ASSERT_TRUE(d.Build(kDeepSrc));
  d.Annotate(SdfDelay("(INTERCONNECT u1/b/a/q u2/d (9))"));
  ASSERT_NE(d.Load("u2/d"), nullptr);
  ASSERT_NE(d.Load("u2/m2/d"), nullptr);
  ASSERT_NE(d.Load("u2/m2/m1/d"), nullptr);
  EXPECT_EQ(d.Load("u2/d")->delays[0], 9u);
  EXPECT_EQ(d.Load("u2/m2/d")->delays[0], 9u);
  EXPECT_EQ(d.Load("u2/m2/m1/d")->delays[0], 9u);
}

TEST(SdfInterconnectAnnotation, UpHierarchyAnnotationReachesPortsAboveTheLoad) {
  Design d;
  ASSERT_TRUE(d.Build(kDeepSrc));
  d.Annotate(SdfDelay("(INTERCONNECT u1/b/a/q u2/m2/d (6))"));
  const auto* above = d.mgr.FindInterconnectDelay("u1/b/a/q", "u2/d");
  ASSERT_NE(above, nullptr);
  EXPECT_EQ(above->delays[0], 6u);
  ASSERT_NE(d.Load("u2/m2/d"), nullptr);
  EXPECT_EQ(d.Load("u2/m2/d")->delays[0], 6u);
}

TEST(SdfInterconnectAnnotation, DownHierarchyAnnotationIsFromSourcesAbove) {
  Design d;
  ASSERT_TRUE(d.Build(kDeepSrc));
  d.Annotate(SdfDelay("(INTERCONNECT u1/b/q u2/m2/m1/d (4))"));
  const auto* named = d.mgr.FindInterconnectDelay("u1/b/q", "u2/m2/m1/d");
  const auto* above = d.mgr.FindInterconnectDelay("u1/q", "u2/m2/m1/d");
  ASSERT_NE(named, nullptr);
  ASSERT_NE(above, nullptr);
  EXPECT_EQ(above->delays[0], 4u);
}

TEST(SdfInterconnectAnnotation, SourceCoverageFollowsTheHierarchyNotTheDepth) {
  Design d;
  ASSERT_TRUE(
      d.Build("module drv(q);\n"
              "  output q;\n"
              "  reg q;\n"
              "endmodule\n"
              "module wrap(q);\n"
              "  output q;\n"
              "  wire q;\n"
              "  drv s(.q(q));\n"
              "endmodule\n"
              "module ld(d);\n"
              "  input d;\n"
              "  wire d;\n"
              "endmodule\n"
              "module top;\n"
              "  wire w;\n"
              "  wrap u1(.q(w));\n"
              "  drv u3(.q(w));\n"
              "  ld u2(.d(w));\n"
              "endmodule\n"));
  d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/d (5))"));
  const auto* below = d.mgr.FindInterconnectDelay("u1/s/q", "u2/d");
  ASSERT_NE(below, nullptr);
  EXPECT_EQ(below->delays[0], 5u);
  EXPECT_EQ(d.mgr.FindInterconnectDelay("u3/q", "u2/d"), nullptr);
}

TEST(SdfInterconnectAnnotation, ValueStatingItsPulseLimitsIsRead) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/d ((5) (2) (3)))"));
  EXPECT_TRUE(result.warnings.empty());
  const auto* got = d.Load("u2/d");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 5u);
  EXPECT_EQ(got->reject_limit[0], 2u);
  EXPECT_EQ(got->error_limit[0], 3u);
}

TEST(SdfInterconnectAnnotation, EmptyValueHoldsTheDelayInForce) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  d.Annotate(
      SdfDelay("(INTERCONNECT u1/q u2/d (6) (6))"
               " (INTERCONNECT u1/q u2/d () (7))"));
  const auto* got = d.Load("u2/d");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 6u);
  EXPECT_EQ(got->delays[1], 7u);
}

TEST(SdfInterconnectAnnotation, OverlappingAnnotationsResolveToTheirSubsets) {
  Design d;
  ASSERT_TRUE(d.Build(kDeepSrc));
  d.Annotate(
      SdfDelay("(INTERCONNECT u1/b/a/q u2/d (3))"
               " (INTERCONNECT u1/b/a/q u2/m2/m1/d (7))"));
  ASSERT_NE(d.Load("u2/d"), nullptr);
  ASSERT_NE(d.Load("u2/m2/d"), nullptr);
  ASSERT_NE(d.Load("u2/m2/m1/d"), nullptr);
  EXPECT_EQ(d.Load("u2/d")->delays[0], 3u);
  EXPECT_EQ(d.Load("u2/m2/d")->delays[0], 3u);
  EXPECT_EQ(d.Load("u2/m2/m1/d")->delays[0], 7u);
}

TEST(SdfInterconnectAnnotation, TwoValueEntryFillsTwelveTransitions) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/d (7) (11))"));
  const auto* got = d.Load("u2/d");
  ASSERT_NE(got, nullptr);
  const uint64_t kExpected[12] = {7, 11, 7, 7, 11, 11, 7, 7, 11, 11, 11, 7};
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(got->delays[i], kExpected[i]) << "slot " << i;
  }
}

TEST(SdfInterconnectAnnotation, ThreeValueEntryFillsTwelveTransitions) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/d (4) (6) (9))"));
  const auto* got = d.Load("u2/d");
  ASSERT_NE(got, nullptr);
  const uint64_t kExpected[12] = {4, 6, 9, 4, 9, 6, 4, 4, 6, 6, 9, 4};
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(got->delays[i], kExpected[i]) << "slot " << i;
  }
}

TEST(SdfInterconnectAnnotation, SixValueEntryFillsItsSixTransitionsDirectly) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/d (1) (2) (3) (4) (5) (6))"));
  const auto* got = d.Load("u2/d");
  ASSERT_NE(got, nullptr);
  for (int i = 0; i < 6; ++i) {
    EXPECT_EQ(got->delays[i], static_cast<uint64_t>(i + 1)) << "slot " << i;
  }
}

TEST(SdfInterconnectAnnotation, TwelveValueEntryFillsEverySlotDirectly) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  d.Annotate(SdfDelay(
      "(INTERCONNECT u1/q u2/d (1) (2) (3) (4) (5) (6) (7) (8) (9) (10) (11)"
      " (12))"));
  const auto* got = d.Load("u2/d");
  ASSERT_NE(got, nullptr);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(got->delays[i], static_cast<uint64_t>(i + 1)) << "slot " << i;
  }
}

TEST(SdfInterconnectAnnotation, MinTypMaxDelayValueSelectsTheMinimum) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/d (2:5:9))"), SdfMtm::kMinimum);
  const auto* got = d.Load("u2/d");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 2u);
}

TEST(SdfInterconnectAnnotation, MinTypMaxDelayValueSelectsTheMaximum) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/d (2:5:9))"), SdfMtm::kMaximum);
  const auto* got = d.Load("u2/d");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 9u);
}

TEST(SdfInterconnectAnnotation, PulseLimitsFollowThePercentagesInEffect) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  d.mgr.SetGlobalPulseLimitPercents(50, 75);
  d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/d (8) (12))"));
  const auto* got = d.Load("u2/d");
  ASSERT_NE(got, nullptr);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(got->reject_limit[i], got->delays[i] * 50 / 100) << "slot " << i;
    EXPECT_EQ(got->error_limit[i], got->delays[i] * 75 / 100) << "slot " << i;
  }
  EXPECT_EQ(got->reject_limit[0], 4u);
  EXPECT_EQ(got->reject_limit[1], 6u);
  EXPECT_EQ(got->error_limit[0], 6u);
  EXPECT_EQ(got->error_limit[1], 9u);
}

TEST(SdfInterconnectAnnotation, EachTransitionCarriesItsOwnPulseLimits) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/d (7) (11))"));
  const auto* got = d.Load("u2/d");
  ASSERT_NE(got, nullptr);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(got->reject_limit[i], got->delays[i]) << "slot " << i;
    EXPECT_EQ(got->error_limit[i], got->delays[i]) << "slot " << i;
  }
}

TEST(SdfInterconnectAnnotation, ReferenceToTheLoadReadsTheDelayedValue) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/d (3) (7))"));
  const auto kAtLoad = d.mgr.ReadInterconnectReference("u2/d");
  EXPECT_TRUE(kAtLoad.delayed);
  EXPECT_EQ(kAtLoad.delay, 3u);
  EXPECT_EQ(kAtLoad.load_port, "u2/d");
}

TEST(SdfInterconnectAnnotation, ReferenceToTheSourceReadsTheUndelayedValue) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/d (3) (7))"));
  EXPECT_FALSE(d.mgr.ReadInterconnectReference("u1/q").delayed);
  EXPECT_FALSE(d.mgr.ReadInterconnectReference("n").delayed);
}

TEST(SdfInterconnectAnnotation, ReferencesBeforeAndAfterTheLoadDiffer) {
  Design d;
  ASSERT_TRUE(d.Build(kDeepSrc));
  d.Annotate(SdfDelay("(INTERCONNECT u1/b/a/q u2/m2/d (5))"));
  EXPECT_TRUE(d.mgr.ReadInterconnectReference("u2/m2/m1/d").delayed);
  EXPECT_FALSE(d.mgr.ReadInterconnectReference("u1/b/q").delayed);
}

TEST(SdfInterconnectAnnotation, SingleValueEntryBroadcastsAcrossAllSlots) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/d (5))"));
  const auto* got = d.Load("u2/d");
  ASSERT_NE(got, nullptr);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(got->delays[i], 5u) << "slot " << i;
  }
}

}  // namespace
