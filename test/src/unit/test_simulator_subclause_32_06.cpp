#include <gtest/gtest.h>

#include <fstream>
#include <ios>
#include <string>
#include <vector>

#include "fixture_sdf_design.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// §32.6 is about what a *run* of $sdf_annotate calls does, so the state each
// call finds already in place -- what the module path was declared to hold and
// what earlier calls left on it -- is part of every test's input. Each test
// therefore builds its SystemVerilog side from real source (parsed, elaborated
// and lowered, with the declared paths handed to the production collector) and
// its SDF side from real SDF text written to real files, then runs the design
// so the $sdf_annotate calls the source writes are the things that drive the
// annotation. Nothing on either side is hand-assembled.
struct Design : SdfDesign {
  bool Build(const std::string& src) {
    if (!SdfDesign::Lower(src)) return false;
    const ModuleDecl& top = Top();
    // §32.6 speaks of annotated *values*, not of module path delays alone, so
    // the declared specparams and timing checks are collected alongside the
    // paths and each of the three can be watched across a run of calls.
    mgr.BindDesignSpecparams(CollectDeclaredSpecparams(top), f.ctx, f.arena);
    AddPathsAndTimingChecks(top);
    // §32.9: a $sdf_annotate call reaches the design's specify data through the
    // running context, so binding the manager here is what lets the calls the
    // source writes annotate this design.
    f.ctx.SetSpecifyManager(&mgr);
    return true;
  }

  void Run() { f.scheduler.Run(); }

  uint64_t Delay(std::string_view src, std::string_view dst) const {
    for (const auto& pd : mgr.GetPathDelays()) {
      if (pd.src_port == src && pd.dst_port == dst) return pd.delays[0];
    }
    return 0;
  }

  const TimingCheckEntry* Check(TimingCheckKind kind) const {
    for (const auto& tc : mgr.GetTimingChecks()) {
      if (tc.kind == kind) return &tc;
    }
    return nullptr;
  }

  uint64_t Specparam(std::string_view name) const {
    for (const auto& sp : mgr.GetSpecparamValues()) {
      if (sp.name == name) return sp.value;
    }
    return 0;
  }
};

// Puts one SDF file on disk under the name the SystemVerilog source will open,
// since the sdf_file argument names a file rather than carrying its text.
std::string WriteSdf(const std::string& name, const std::string& text) {
  const std::string kPath = std::string("/tmp/delta_c32_06_") + name;
  std::ofstream out(kPath, std::ios::trunc);
  out << text;
  out.close();
  return kPath;
}

// A design with two module paths, each in its own instance of the same leaf
// cell, so a call can be aimed at one region and leave the other alone. Both
// paths start at 0 so any nonzero delay came from an annotation.
const char* const kTwoRegionSrc =
    "module leaf(input I, output O);\n"
    "endmodule\n"
    "module top(input A, input B, output Z, output Y);\n"
    "  leaf a(A, Z);\n"
    "  leaf b(B, Y);\n"
    "  specify\n"
    "    (A => Z) = 0;\n"
    "    (B => Y) = 0;\n"
    "  endspecify\n"
    "  initial begin\n"
    "    $sdf_annotate(\"@F1@\", top.a);\n"
    "    $sdf_annotate(\"@F2@\", top.b);\n"
    "  end\n"
    "endmodule\n";

// Substitutes the file names the test wrote into the source's calls, so the
// calls are ordinary source text naming ordinary files.
std::string WithFiles(std::string src, const std::string& f1,
                      const std::string& f2) {
  const std::size_t k1 = src.find("@F1@");
  src.replace(k1, 4, f1);
  const std::size_t k2 = src.find("@F2@");
  src.replace(k2, 4, f2);
  return src;
}

// More than one SDF file can be annotated, and each call annotates the design
// with the timing its own file carries. Two files, each holding one of the
// design's two module paths, both land.
TEST(SdfMultipleFiles, EachCallAnnotatesTheDesignFromItsOwnFile) {
  const std::string kF1 = WriteSdf("each_1.sdf",
                                   "(DELAYFILE (CELL (CELLTYPE \"leaf\") "
                                   "(INSTANCE top/a) (DELAY (ABSOLUTE (IOPATH "
                                   "A Z (10))))))");
  const std::string kF2 = WriteSdf("each_2.sdf",
                                   "(DELAYFILE (CELL (CELLTYPE \"leaf\") "
                                   "(INSTANCE top/b) (DELAY (ABSOLUTE (IOPATH "
                                   "B Y (20))))))");

  Design d;
  ASSERT_TRUE(d.Build(WithFiles(kTwoRegionSrc, kF1, kF2)));
  d.Run();

  EXPECT_EQ(d.Delay("A", "Z"), 10u);
  EXPECT_EQ(d.Delay("B", "Y"), 20u);

  // Each call is one annotation of the design from one file, recorded in the
  // order the calls ran.
  ASSERT_EQ(d.mgr.GetSdfAnnotations().size(), 2u);
  EXPECT_EQ(d.mgr.GetSdfAnnotations()[0].sdf_file, kF1);
  EXPECT_EQ(d.mgr.GetSdfAnnotations()[1].sdf_file, kF2);
}

// An ABSOLUTE value in a later file overwrites what an earlier file annotated
// onto the same path.
TEST(SdfMultipleFiles, AbsoluteValueOverwritesWhatAnEarlierFileAnnotated) {
  const std::string kF1 = WriteSdf("abs_1.sdf",
                                   "(DELAYFILE (CELL (CELLTYPE \"leaf\") "
                                   "(INSTANCE top/a) (DELAY (ABSOLUTE (IOPATH "
                                   "A Z (5))))))");
  const std::string kF2 = WriteSdf("abs_2.sdf",
                                   "(DELAYFILE (CELL (CELLTYPE \"leaf\") "
                                   "(INSTANCE top/a) (DELAY (ABSOLUTE (IOPATH "
                                   "A Z (9))))))");

  // Both calls are aimed at the same region so the second file reaches the
  // path the first one annotated.
  const char* const kSrc =
      "module leaf(input I, output O);\n"
      "endmodule\n"
      "module top(input A, output Z);\n"
      "  leaf a(A, Z);\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "  endspecify\n"
      "  initial begin\n"
      "    $sdf_annotate(\"@F1@\", top.a);\n"
      "    $sdf_annotate(\"@F2@\", top.a);\n"
      "  end\n"
      "endmodule\n";

  Design d;
  ASSERT_TRUE(d.Build(WithFiles(kSrc, kF1, kF2)));
  d.Run();

  EXPECT_EQ(d.Delay("A", "Z"), 9u);
}

// An INCREMENT value in a later file modifies what an earlier file annotated
// rather than replacing it.
TEST(SdfMultipleFiles, IncrementValueModifiesWhatAnEarlierFileAnnotated) {
  const std::string kF1 = WriteSdf("inc_1.sdf",
                                   "(DELAYFILE (CELL (CELLTYPE \"leaf\") "
                                   "(INSTANCE top/a) (DELAY (ABSOLUTE (IOPATH "
                                   "A Z (5))))))");
  const std::string kF2 = WriteSdf("inc_2.sdf",
                                   "(DELAYFILE (CELL (CELLTYPE \"leaf\") "
                                   "(INSTANCE top/a) (DELAY (INCREMENT (IOPATH "
                                   "A Z (3))))))");

  const char* const kSrc =
      "module leaf(input I, output O);\n"
      "endmodule\n"
      "module top(input A, output Z);\n"
      "  leaf a(A, Z);\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "  endspecify\n"
      "  initial begin\n"
      "    $sdf_annotate(\"@F1@\", top.a);\n"
      "    $sdf_annotate(\"@F2@\", top.a);\n"
      "  end\n"
      "endmodule\n";

  Design d;
  ASSERT_TRUE(d.Build(WithFiles(kSrc, kF1, kF2)));
  d.Run();

  EXPECT_EQ(d.Delay("A", "Z"), 8u);
}

// The same INCREMENT file annotated twice modifies the design twice, which is
// what "each call annotates the design" means when the two calls name one file.
TEST(SdfMultipleFiles, RepeatingOneIncrementFileModifiesTheDesignEachTime) {
  const std::string kF1 = WriteSdf("rep_1.sdf",
                                   "(DELAYFILE (CELL (CELLTYPE \"leaf\") "
                                   "(INSTANCE top/a) (DELAY (ABSOLUTE (IOPATH "
                                   "A Z (5))))))");
  const std::string kF2 = WriteSdf("rep_2.sdf",
                                   "(DELAYFILE (CELL (CELLTYPE \"leaf\") "
                                   "(INSTANCE top/a) (DELAY (INCREMENT (IOPATH "
                                   "A Z (3))))))");

  const char* const kSrc =
      "module leaf(input I, output O);\n"
      "endmodule\n"
      "module top(input A, output Z);\n"
      "  leaf a(A, Z);\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "  endspecify\n"
      "  initial begin\n"
      "    $sdf_annotate(\"@F1@\", top.a);\n"
      "    $sdf_annotate(\"@F2@\", top.a);\n"
      "    $sdf_annotate(\"@F2@\", top.a);\n"
      "  end\n"
      "endmodule\n";

  std::string src = WithFiles(kSrc, kF1, kF2);
  const std::size_t kThird = src.find("@F2@");
  src.replace(kThird, 4, kF2);

  Design d;
  ASSERT_TRUE(d.Build(src));
  d.Run();

  EXPECT_EQ(d.Delay("A", "Z"), 11u);
  EXPECT_EQ(d.mgr.GetSdfAnnotations().size(), 3u);
}

// Different regions of a design can be annotated from different SDF files, by
// naming the region's hierarchy scope as the second argument. Each file here
// carries entries for both regions, and each call takes only the entries that
// fall inside the region it names.
TEST(SdfMultipleFiles,
     SecondArgumentAnnotatesDifferentRegionsFromDifferentFiles) {
  const std::string kF1 = WriteSdf("region_1.sdf",
                                   "(DELAYFILE"
                                   " (CELL (CELLTYPE \"leaf\") (INSTANCE top/a)"
                                   "   (DELAY (ABSOLUTE (IOPATH A Z (10)))))"
                                   " (CELL (CELLTYPE \"leaf\") (INSTANCE top/b)"
                                   "   (DELAY (ABSOLUTE (IOPATH B Y (11))))))");
  const std::string kF2 = WriteSdf("region_2.sdf",
                                   "(DELAYFILE"
                                   " (CELL (CELLTYPE \"leaf\") (INSTANCE top/a)"
                                   "   (DELAY (ABSOLUTE (IOPATH A Z (20)))))"
                                   " (CELL (CELLTYPE \"leaf\") (INSTANCE top/b)"
                                   "   (DELAY (ABSOLUTE (IOPATH B Y (21))))))");

  Design d;
  ASSERT_TRUE(d.Build(WithFiles(kTwoRegionSrc, kF1, kF2)));
  d.Run();

  // Region top/a took its delay from the first file only, and region top/b
  // from the second file only.
  EXPECT_EQ(d.Delay("A", "Z"), 10u);
  EXPECT_EQ(d.Delay("B", "Y"), 21u);
}

// Two files, the later one INCREMENT, aimed at two different regions: the
// increment modifies only the region it names, so the other region keeps the
// value the earlier file gave it without any increment applied.
TEST(SdfMultipleFiles, IncrementInALaterFileReachesOnlyTheRegionItNames) {
  const std::string kF1 = WriteSdf("regioninc_1.sdf",
                                   "(DELAYFILE"
                                   " (CELL (CELLTYPE \"leaf\") (INSTANCE top/a)"
                                   "   (DELAY (ABSOLUTE (IOPATH A Z (4)))))"
                                   " (CELL (CELLTYPE \"leaf\") (INSTANCE top/b)"
                                   "   (DELAY (ABSOLUTE (IOPATH B Y (4))))))");
  const std::string kF2 = WriteSdf("regioninc_2.sdf",
                                   "(DELAYFILE"
                                   " (CELL (CELLTYPE \"leaf\") (INSTANCE top/a)"
                                   "   (DELAY (INCREMENT (IOPATH A Z (6)))))"
                                   " (CELL (CELLTYPE \"leaf\") (INSTANCE top/b)"
                                   "   (DELAY (INCREMENT (IOPATH B Y (6))))))");

  const char* const kSrc =
      "module leaf(input I, output O);\n"
      "endmodule\n"
      "module top(input A, input B, output Z, output Y);\n"
      "  leaf a(A, Z);\n"
      "  leaf b(B, Y);\n"
      "  specify\n"
      "    (A => Z) = 0;\n"
      "    (B => Y) = 0;\n"
      "  endspecify\n"
      "  initial begin\n"
      "    $sdf_annotate(\"@F1@\");\n"
      "    $sdf_annotate(\"@F2@\", top.a);\n"
      "  end\n"
      "endmodule\n";

  Design d;
  ASSERT_TRUE(d.Build(WithFiles(kSrc, kF1, kF2)));
  d.Run();

  EXPECT_EQ(d.Delay("A", "Z"), 10u);
  EXPECT_EQ(d.Delay("B", "Y"), 4u);
}

// A design whose annotatable value is a timing check constraint rather than a
// module path delay, so what one file left for a later file to overwrite is a
// constraint limit.
const char* const kCheckSrc =
    "module leaf(input I, output O);\n"
    "endmodule\n"
    "module top(input D, input CK, output Z);\n"
    "  leaf a(D, Z);\n"
    "  specify\n"
    "    $setup(posedge CK, D, 5);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    $sdf_annotate(\"@F1@\", top.a);\n"
    "    $sdf_annotate(\"@F2@\", top.a);\n"
    "  end\n"
    "endmodule\n";

// "Annotated values" is not confined to module path delays: a constraint limit
// an earlier file annotated is overwritten by a later file's ABSOLUTE value the
// same way a delay is.
TEST(SdfMultipleFiles, AbsoluteValueOverwritesAConstraintFromAnEarlierFile) {
  const std::string kF1 =
      WriteSdf("check_1.sdf",
               "(DELAYFILE (CELL (CELLTYPE \"leaf\") (INSTANCE top/a)"
               " (TIMINGCHECK (SETUP D (posedge CK) (12)))))");
  const std::string kF2 =
      WriteSdf("check_2.sdf",
               "(DELAYFILE (CELL (CELLTYPE \"leaf\") (INSTANCE top/a)"
               " (TIMINGCHECK (SETUP D (posedge CK) (30)))))");

  Design d;
  ASSERT_TRUE(d.Build(WithFiles(kCheckSrc, kF1, kF2)));
  ASSERT_NE(d.Check(TimingCheckKind::kSetup), nullptr);
  ASSERT_EQ(d.Check(TimingCheckKind::kSetup)->limit, 5u);

  d.Run();

  EXPECT_EQ(d.Check(TimingCheckKind::kSetup)->limit, 30u);
}

// A design whose annotatable value is a specparam the module declares, the
// third category of value a run of SDF files can leave state in.
const char* const kSpecparamSrc =
    "module leaf(input I, output O);\n"
    "endmodule\n"
    "module top(input A, output Z);\n"
    "  leaf a(A, Z);\n"
    "  specify\n"
    "    specparam cap = 4;\n"
    "    (A => Z) = cap;\n"
    "  endspecify\n"
    "  initial begin\n"
    "    $sdf_annotate(\"@F1@\", top.a);\n"
    "    $sdf_annotate(\"@F2@\", top.a);\n"
    "  end\n"
    "endmodule\n";

// A later file's INCREMENT modifies the specparam value an earlier file
// annotated, and the module path delay whose expression reads that specparam
// follows it, so the modification is visible on both.
TEST(SdfMultipleFiles, IncrementModifiesASpecparamFromAnEarlierFile) {
  const std::string kF1 =
      WriteSdf("label_1.sdf",
               "(DELAYFILE (CELL (CELLTYPE \"leaf\") (INSTANCE top/a)"
               " (LABEL (ABSOLUTE (cap 20)))))");
  const std::string kF2 =
      WriteSdf("label_2.sdf",
               "(DELAYFILE (CELL (CELLTYPE \"leaf\") (INSTANCE top/a)"
               " (LABEL (INCREMENT (cap 7)))))");

  Design d;
  ASSERT_TRUE(d.Build(WithFiles(kSpecparamSrc, kF1, kF2)));
  ASSERT_EQ(d.Delay("A", "Z"), 4u);

  d.Run();

  EXPECT_EQ(d.Specparam("cap"), 27u);
  EXPECT_EQ(d.Delay("A", "Z"), 27u);
}

}  // namespace
