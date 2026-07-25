#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// §32.4.4 has no SystemVerilog declaration behind it: an interconnect delay is
// annotated between the module ports of a design, so which ports exist, which
// way they face and which net they sit on is the whole subject. Every test that
// exercises a matching rule therefore builds its design from real source --
// Design parses, elaborates and lowers it, and hands the production collector
// the module hierarchy it produced -- and its SDF side from real SDF text
// handed to ParseSdf. Nothing on either side is hand-assembled.
struct Design {
  SimFixture f;
  SpecifyManager mgr;
  CompilationUnit* cu = nullptr;
  RtlirDesign* design = nullptr;

  bool Build(const std::string& src) {
    auto fid = f.mgr.AddFile("<test>", src);
    Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
    Parser parser(lexer, f.arena, f.diag);
    cu = parser.Parse();
    if (cu == nullptr || cu->modules.empty()) return false;
    Elaborator elab(f.arena, f.diag, cu);
    design = elab.Elaborate(cu->modules.back()->name);
    if (design == nullptr) return false;

    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);

    mgr.BindDesignInterconnect(
        CollectInterconnectTopology(*cu, *cu->modules.back()));
    return true;
  }

  SdfAnnotationResult Annotate(const std::string& sdf,
                               SdfMtm mtm = SdfMtm::kTypical) {
    SdfFile file;
    EXPECT_TRUE(ParseSdf(sdf, file));
    return AnnotateSdfToManager(file, mgr, mtm);
  }

  // The delay annotated onto one load, whatever source it was recorded as
  // coming from.
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

// Wraps a DELAY body in the DELAYFILE/CELL structure an SDF file always
// supplies, so each test writes only the entries under test.
std::string SdfDelay(const std::string& body, const std::string& version = {}) {
  std::string out = "(DELAYFILE ";
  if (!version.empty()) out += "(SDFVERSION \"" + version + "\") ";
  out += "(CELL (CELLTYPE \"top\") (INSTANCE top) (DELAY (ABSOLUTE " + body +
         "))))";
  return out;
}

// One source instance driving one load instance over a net of the top module --
// the simplest shape an interconnect delay can be annotated across.
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

// Two source instances and two load instances on one net of the top module.
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

// One net carried three levels down on both sides, so a source and a load can
// each be named at any of three hierarchical depths.
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

// An inout port is admitted on both ends of an interconnect delay: it may be
// the source and it may be the load, so the same port serves as both here.
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

// A source driving one net, and a separate net with two sources and a load, so
// an entry can name a source that exists but sits on the wrong net.
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

// ---------------------------------------------------------------------------
// The three constructs of Table 32-3 and what each one carries.
// ---------------------------------------------------------------------------

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

// Table 32-3 footnote: NETDELAY belongs only to OVI SDF 1.0, 2.0 and 2.1 and to
// IEEE SDF 4.0, so a file declaring another version carries data the annotator
// will not take in.
TEST(SdfInterconnectAnnotation, NetdelayIsAnnotatedForAVersionThatDefinesIt) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(NETDELAY u2/d (4))", "2.1"));
  EXPECT_FALSE(d.AnyWarningMentions(result, "NETDELAY"));
  ASSERT_NE(d.Load("u2/d"), nullptr);
  EXPECT_EQ(d.Load("u2/d")->delays[0], 4u);
}

// The IEEE SDF version is the other one the footnote lists.
TEST(SdfInterconnectAnnotation, NetdelayIsAnnotatedForTheIeeeSdfVersion) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(NETDELAY u2/d (4))", "4.0"));
  EXPECT_FALSE(d.AnyWarningMentions(result, "NETDELAY"));
  ASSERT_NE(d.Load("u2/d"), nullptr);
  EXPECT_EQ(d.Load("u2/d")->delays[0], 4u);
}

// A file that names no version at all says nothing about which constructs it
// carries, so its NETDELAY entry is taken at face value.
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

// ---------------------------------------------------------------------------
// Interconnect delays go between module ports and never between primitive pins.
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// PORT: search for the port and annotate the delay from all sources to it.
// ---------------------------------------------------------------------------

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

// A PORT delay stands for the delay from every source on the net, so it answers
// for a source the entry never named.
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

// A PORT entry annotates a port. A net is what the NETDELAY entry may name
// instead, so a PORT entry naming one reaches nothing.
TEST(SdfInterconnectAnnotation, PortConstructNamingANetIsWarnedAbout) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(PORT n (5))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "names no port"));
  EXPECT_TRUE(d.mgr.GetInterconnectDelays().empty());
}

// A load port shall be an input or an inout port, so an output port is not one.
TEST(SdfInterconnectAnnotation, PortConstructNamingAnOutputPortIsWarnedAbout) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(PORT u1/q (3))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "not an input or inout"));
  EXPECT_TRUE(d.mgr.GetInterconnectDelays().empty());
}

// ---------------------------------------------------------------------------
// NETDELAY: work out whether the name is a port or a net first.
// ---------------------------------------------------------------------------

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

// On a net with more than one source the delay stands for the delay from all of
// them.
TEST(SdfInterconnectAnnotation, NetdelayOnAMultisourceNetIsFromAllSources) {
  Design d;
  ASSERT_TRUE(d.Build(kMultisourceSrc));
  d.Annotate(SdfDelay("(NETDELAY n (7))"));
  EXPECT_NE(d.mgr.FindInterconnectDelay("s1/q", "l2/d"), nullptr);
  EXPECT_NE(d.mgr.FindInterconnectDelay("s2/q", "l2/d"), nullptr);
}

// The same holds when the NETDELAY names a port rather than the net: a port
// fed by more than one source carries the delay from all of them.
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

// ---------------------------------------------------------------------------
// INTERCONNECT: a unique delay per source/load pair, and what happens when the
// source cannot be placed.
// ---------------------------------------------------------------------------

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

// On a multisource net each source/load pair can carry its own delay.
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

// The load is the end the annotator cannot do without: with no load port of
// that name there is nowhere for the delay to go.
TEST(SdfInterconnectAnnotation, InterconnectNamingNoLoadPortIsWarnedAbout) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT u1/q absent/d (4))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "names no load port"));
  EXPECT_TRUE(d.mgr.GetInterconnectDelays().empty());
}

// An INTERCONNECT entry may name a net as its load, which stands for the load
// ports of that net rather than for one port.
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

// A source that is not found is warned about, but the delay still reaches the
// load.
TEST(SdfInterconnectAnnotation, MissingSourceWarnsAndStillAnnotatesTheLoad) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT u9/q u2/d (4))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "not found"));
  const auto* got = d.Load("u2/d");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 4u);
}

// The same on a multisource net: the delay is then taken as the delay from all
// sources, which is what a PORT delay is.
TEST(SdfInterconnectAnnotation,
     MissingSourceOnAMultisourceNetBecomesFromAllSources) {
  Design d;
  ASSERT_TRUE(d.Build(kMultisourceSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT nowhere/q l1/d (4))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "not found"));
  EXPECT_NE(d.mgr.FindInterconnectDelay("s1/q", "l1/d"), nullptr);
  EXPECT_NE(d.mgr.FindInterconnectDelay("s2/q", "l1/d"), nullptr);
}

// On a single-source net the delay stays the delay from the source the entry
// named, so it does not answer for the net's real source.
TEST(SdfInterconnectAnnotation,
     MissingSourceOnASingleSourceNetStaysFromThatSource) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  d.Annotate(SdfDelay("(INTERCONNECT u9/q u2/d (4))"));
  EXPECT_NE(d.mgr.FindInterconnectDelay("u9/q", "u2/d"), nullptr);
  EXPECT_EQ(d.mgr.FindInterconnectDelay("u1/q", "u2/d"), nullptr);
}

// A source and a load that are not actually on the same net is warned about
// too, and the delay is annotated to the load anyway.
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

// A source port shall be an output or an inout port.
TEST(SdfInterconnectAnnotation, InputSourcePortIsWarnedAbout) {
  Design d;
  ASSERT_TRUE(d.Build(kMultisourceSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT l2/d l1/d (5))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "not an output or inout port"));
}

// A load port shall be an input or an inout port.
TEST(SdfInterconnectAnnotation, OutputLoadPortIsWarnedAboutAndNotAnnotated) {
  Design d;
  ASSERT_TRUE(d.Build(kMultisourceSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT s1/q s2/q (5))"));
  EXPECT_TRUE(d.AnyWarningMentions(result, "not an input or inout port"));
  EXPECT_EQ(d.Load("s2/q"), nullptr);
}

// An inout port is one of the two kinds a load may be, so a delay to one is
// annotated without complaint.
TEST(SdfInterconnectAnnotation, InoutPortIsAcceptedAsALoad) {
  Design d;
  ASSERT_TRUE(d.Build(kInoutSrc));
  auto result = d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/io (4))"));
  EXPECT_FALSE(d.AnyWarningMentions(result, "not an input or inout"));
  const auto* got = d.mgr.FindInterconnectDelay("u1/q", "u2/io");
  ASSERT_NE(got, nullptr);
  EXPECT_EQ(got->delays[0], 4u);
}

// An inout port is likewise one of the two kinds a source may be.
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

// The other way an INTERCONNECT source fails to place: it exists, but the net
// it sits on is not the load's. On a load whose net has several sources the
// delay then stands for the delay from all of them, as a PORT delay does.
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

// ---------------------------------------------------------------------------
// Hierarchy: an annotation reaches the connected ports at other levels.
// ---------------------------------------------------------------------------

// An annotation to a port affects the connected ports below it as well.
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

// Up-hierarchy annotation, where the load sits above the source: the delay to
// every port above the load is the delay to that load.
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

// Down-hierarchy annotation, where the source sits above the load: the delay is
// from every source at or above the one the entry named.
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

// Hierarchically overlapping annotations: the first covers every port of the
// net at or within the load it names, and the second, naming a smaller subset,
// changes only the ports of that subset.
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

// ---------------------------------------------------------------------------
// Twelve transition delays, filled in and pulse-limited like a path delay.
// ---------------------------------------------------------------------------

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
  const uint64_t kExpected[12] = {4, 6, 9, 4, 9, 6, 4, 9, 6, 6, 9, 4};
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

// A delay value of an interconnect entry may be a min:typ:max triple, and which
// member fills the transition slots is the selection the run asked for.
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

// An interconnect delay takes its pulse limits by the rule a specify path delay
// follows, so the pulse-limit percentages in effect reach it too, and each
// transition's limits come from that transition's own delay.
TEST(SdfInterconnectAnnotation, PulseLimitsFollowThePercentagesInEffect) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  d.mgr.SetGlobalPulseLimitPercents(/*reject_pct=*/50, /*error_pct=*/75);
  d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/d (8) (12))"));
  const auto* got = d.Load("u2/d");
  ASSERT_NE(got, nullptr);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(got->reject_limit[i], got->delays[i] * 50 / 100) << "slot " << i;
    EXPECT_EQ(got->error_limit[i], got->delays[i] * 75 / 100) << "slot " << i;
  }
  // The rise and fall transitions carry different delays, so their limits
  // differ as well rather than sharing one value.
  EXPECT_EQ(got->reject_limit[0], 4u);
  EXPECT_EQ(got->reject_limit[1], 6u);
  EXPECT_EQ(got->error_limit[0], 6u);
  EXPECT_EQ(got->error_limit[1], 9u);
}

// Each of the twelve transitions carries its own reject and error pulse limit.
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

// ---------------------------------------------------------------------------
// What a reference reads: delayed at or after the load, undelayed before it.
// ---------------------------------------------------------------------------

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

// A reference hierarchically after the load reads the delayed value too, while
// one hierarchically before it does not.
TEST(SdfInterconnectAnnotation, ReferencesBeforeAndAfterTheLoadDiffer) {
  Design d;
  ASSERT_TRUE(d.Build(kDeepSrc));
  d.Annotate(SdfDelay("(INTERCONNECT u1/b/a/q u2/m2/d (5))"));
  EXPECT_TRUE(d.mgr.ReadInterconnectReference("u2/m2/m1/d").delayed);
  EXPECT_FALSE(d.mgr.ReadInterconnectReference("u1/b/q").delayed);
}

// The delay running: the source's transition reaches the load the annotated
// delay later, and the rise and fall transitions take their own slot's delay.
TEST(SdfInterconnectAnnotation, SourceTransitionsArriveAtTheLoadDelayed) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/d (3) (7))"));
  d.mgr.StartInterconnectPropagation(d.f.ctx, d.f.scheduler);
  d.f.scheduler.Run();

  const auto& arrivals = d.mgr.GetInterconnectArrivals();
  const InterconnectArrival* rise = nullptr;
  const InterconnectArrival* fall = nullptr;
  for (const auto& a : arrivals) {
    if (a.load_port != "u2/d") continue;
    // The source rises at 5 and falls at 10.
    if (a.value == 1 && a.time == 8) rise = &a;
    if (a.value == 0 && a.time == 17) fall = &a;
  }
  ASSERT_NE(rise, nullptr) << "no delayed rise arrival at the load";
  ASSERT_NE(fall, nullptr) << "no delayed fall arrival at the load";
  EXPECT_EQ(rise->delay, 3u);
  EXPECT_EQ(fall->delay, 7u);
  for (const auto& a : arrivals) {
    // Nothing arrives when the source transitioned: that is the undelayed
    // value, which only a reference to the source reads.
    EXPECT_NE(a.time, 5u);
    EXPECT_NE(a.time, 10u);
  }
}

// Any number of transitions may be in flight at once: a second transition of
// the source does not cancel the first one's pending arrival, even when the two
// arrive out of the order they were sent in.
TEST(SdfInterconnectAnnotation, ManyArrivalsMayBeScheduledAtOnce) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  // The source rises at 5 and falls at 10; a rise takes 20 to reach the load
  // and a fall takes 2, so both are pending together and the later transition
  // arrives first.
  d.Annotate(SdfDelay("(INTERCONNECT u1/q u2/d (20) (2))"));
  d.mgr.StartInterconnectPropagation(d.f.ctx, d.f.scheduler);
  d.f.scheduler.Run();

  bool rise_arrived = false;
  bool fall_arrived = false;
  for (const auto& a : d.mgr.GetInterconnectArrivals()) {
    if (a.load_port != "u2/d") continue;
    if (a.value == 1 && a.time == 25) rise_arrived = true;
    if (a.value == 0 && a.time == 12) fall_arrived = true;
  }
  EXPECT_TRUE(rise_arrived);
  EXPECT_TRUE(fall_arrived);
}

// A delay carrying no source of its own is the delay from every source on the
// load's net, so at run time the load follows whichever source drives that net.
TEST(SdfInterconnectAnnotation, PortAnnotatedLoadFollowsTheNetSourceAtRuntime) {
  Design d;
  ASSERT_TRUE(d.Build(kPairSrc));
  d.Annotate(SdfDelay("(PORT u2/d (4) (6))"));
  d.mgr.StartInterconnectPropagation(d.f.ctx, d.f.scheduler);
  d.f.scheduler.Run();

  bool rise_arrived = false;
  bool fall_arrived = false;
  for (const auto& a : d.mgr.GetInterconnectArrivals()) {
    if (a.load_port != "u2/d") continue;
    // The net's source rises at 5 and falls at 10.
    if (a.value == 1 && a.time == 9) rise_arrived = true;
    if (a.value == 0 && a.time == 16) fall_arrived = true;
  }
  EXPECT_TRUE(rise_arrived);
  EXPECT_TRUE(fall_arrived);
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
