// §32.6 is about what a *run* of $sdf_annotate calls does, so the state each
// call finds already in place -- what the module path was declared to hold and
// what earlier calls left on it -- is part of every test's input. Each test
// therefore builds its SystemVerilog side from real source (parsed, elaborated
// and lowered) and its SDF side from real SDF text written to real files, then
// runs the design so the $sdf_annotate calls the source writes are the things
// that drive the annotation. Nothing on either side is hand-assembled.
//
// The manager every case reads back is the one the run installed --
// SimContext::GetSpecifyManager, which Lowerer::Lower filled through
// SimContext::AcquireSpecifyManager. It is not the standalone SpecifyManager
// that SdfDesign in lib/cpp/test_fixtures/fixture_sdf_design.h carries.
// Binding that one over the top of the installed one, as these cases used to,
// discards what RegisterSpecifyBlocks in src/simulator/specify_register.cpp
// filed: every instance's specify block under its own hierarchical prefix. It
// left every module path standing at the empty prefix a module elaborated as a
// top carries, whatever instance the SDF cell named. Issue #3387 is what that
// hid -- an IOPATH reached every in-scope instance of a cell, because the
// instance the SDF names never reached the PathDelay it keys.
//
// So each design here declares its specify block in the module the SDF cell
// actually names. In the six cases whose cell names an instance, that is the
// instantiated cell, and the path is read back through
// PathDelay::inst_prefix -- "a." for instance a of the top. In the specparam
// case the cell names the top itself, whose prefix is empty, because §32.4.3
// annotates a LABEL to a specparam and SpecifyManager::ApplyAnnotatedSpecparam
// reads that specparam back through SimContext::FindVariable with no instance
// prefix at all.
//
// The literals are picked so that no two quantities a case tells apart share a
// value. Case by case: 10 and 20 for the two instances one call each annotates;
// 5 then 9 for an overwrite; 5 then 3 for an increment, whose 8 is neither; 5,
// 3 and 3 for the repeated increment, whose 11 is reached by no other route; 10
// and 11 against 20 and 21 for the two regions and two files, so a region that
// read the wrong file reads a value nothing else in the case holds; 4 and 6 for
// the region-limited increment, whose 10 stands against the 4 the other region
// keeps; 5, 12 and 30 for the constraint; and 4, 20 and 7 for the specparam,
// whose 27 is distinct from all three. A declared module path starts at 0 and
// every annotated value is nonzero, so an annotation that never happened reads
// as 0 rather than as a right answer. No case reads a delay off a lookup that
// answers 0 when it finds nothing: PathOf returns a pointer, which a case
// asserts on before it reads the delay through it.

#include <gtest/gtest.h>

#include <cstdint>
#include <fstream>
#include <ios>
#include <string>
#include <string_view>

#include "fixture_sdf_design.h"
#include "fixture_simulator.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

// A design carried up to the point where the $sdf_annotate calls its source
// writes can be run, reading its specify data back out of the manager the run
// installed rather than out of one bound over the top of it.
struct Annotated : SdfDesign {
  SpecifyManager* run_mgr = nullptr;

  bool Build(const std::string& src) {
    if (!SdfDesign::Lower(src)) return false;
    run_mgr = f.ctx.GetSpecifyManager();
    return run_mgr != nullptr;
  }

  void Run() { f.scheduler.Run(); }

  // The module the source declares first, which every design here instantiates
  // as its cell.
  const ModuleDecl& Cell() const { return *cu->modules.front(); }

  // §32.6 speaks of annotated *values*, not of module path delays alone, and
  // the run registers only some of them. RegisterSpecifyBlocks files module
  // paths, pulse styles, showcancelled declarations and PATHPULSE$ specparams;
  // a timing check and a specparam binding reach the manager from here, so the
  // constraint case and the specparam case can watch theirs across a run.
  void AddTimingChecksOf(const ModuleDecl& mod) {
    for (auto* item : mod.items) {
      if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
      for (auto* si : item->specify_items) {
        if (si->kind != SpecifyItemKind::kTimingCheck) continue;
        run_mgr->AddTimingCheckUnderOptions(si->timing_check, f.ctx, f.arena);
      }
    }
  }

  void BindSpecparamsOf(const ModuleDecl& mod) {
    run_mgr->BindDesignSpecparams(CollectDeclaredSpecparams(mod), f.ctx,
                                  f.arena);
  }

  // The module path ending at output `dst` of the instance whose hierarchical
  // prefix is `prefix`. Two instances of one cell declare paths spelled the
  // same way, so the prefix is the only thing that separates them, and a null
  // return says the design registered no such path rather than that the path
  // holds nothing.
  const PathDelay* PathOf(std::string_view prefix, std::string_view dst) const {
    for (const auto& pd : run_mgr->GetPathDelays()) {
      if (pd.inst_prefix == prefix && pd.dst_port == dst) return &pd;
    }
    return nullptr;
  }

  const TimingCheckEntry* Check(TimingCheckKind kind) const {
    for (const auto& tc : run_mgr->GetTimingChecks()) {
      if (tc.kind == kind) return &tc;
    }
    return nullptr;
  }

  uint64_t Specparam(std::string_view name) const {
    for (const auto& sp : run_mgr->GetSpecparamValues()) {
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

// The cell whose specify block holds the module path the SDF files annotate.
// §30.4 names a path's terminals by the port names of the module declaring it,
// so every instance of this cell declares a path spelled `in_a => out_z` and
// PathDelay::inst_prefix is what tells two of them apart.
const char* const kIopathCell =
    "module iopath_leaf(input in_a, output out_z);\n"
    "  specify\n"
    "    (in_a => out_z) = 0;\n"
    "  endspecify\n"
    "endmodule\n";

const char* const kOneInstance =
    "  logic first_z;\n"
    "  iopath_leaf a(1'b0, first_z);\n";

const char* const kTwoInstances =
    "  logic first_z;\n"
    "  logic second_z;\n"
    "  iopath_leaf a(1'b0, first_z);\n"
    "  iopath_leaf b(1'b0, second_z);\n";

// The design a case runs: the cell above, the instances of it `instances`
// writes, and the $sdf_annotate calls `calls` writes. The top is named `top`,
// so the scope a call with no module_instance operand works from -- what
// SimContext::CurrentScopeName answers -- is "top", and an SDF instance path
// spelled top/a names instance a below it.
std::string CellDesign(const std::string& instances, const std::string& calls) {
  return std::string(kIopathCell) + "module top;\n" + instances +
         "  initial begin\n" + calls + "  end\nendmodule\n";
}

std::string Call(const std::string& file) {
  return "    $sdf_annotate(\"" + file + "\");\n";
}

std::string CallInScope(const std::string& file, const std::string& scope) {
  return "    $sdf_annotate(\"" + file + "\", " + scope + ");\n";
}

// One CELL record naming instance `inst` of the cell above, annotating that
// instance's module path with `value` under `section` (ABSOLUTE or INCREMENT).
std::string IopathRecord(const std::string& inst, const std::string& section,
                         const std::string& value) {
  return " (CELL (CELLTYPE \"iopath_leaf\") (INSTANCE top/" + inst +
         ") (DELAY (" + section + " (IOPATH in_a out_z (" + value + ")))))";
}

std::string DelayFile(const std::string& records) {
  return "(DELAYFILE" + records + ")";
}

// More than one SDF file can be annotated, and each call annotates the design
// with the timing its own file carries. Two files, each naming one of the two
// instances the design holds, both land.
TEST(SdfMultipleFiles, EachCallAnnotatesTheDesignFromItsOwnFile) {
  const std::string kF1 =
      WriteSdf("each_1.sdf", DelayFile(IopathRecord("a", "ABSOLUTE", "10")));
  const std::string kF2 =
      WriteSdf("each_2.sdf", DelayFile(IopathRecord("b", "ABSOLUTE", "20")));

  Annotated d;
  ASSERT_TRUE(d.Build(CellDesign(kTwoInstances, Call(kF1) + Call(kF2))));
  d.Run();

  const PathDelay* first = d.PathOf("a.", "out_z");
  ASSERT_NE(first, nullptr);
  EXPECT_EQ(first->delays[0], 10u);
  const PathDelay* second = d.PathOf("b.", "out_z");
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(second->delays[0], 20u);

  // Each call is one annotation of the design from one file, recorded in the
  // order the calls ran.
  ASSERT_EQ(d.run_mgr->GetSdfAnnotations().size(), 2u);
  EXPECT_EQ(d.run_mgr->GetSdfAnnotations()[0].sdf_file, kF1);
  EXPECT_EQ(d.run_mgr->GetSdfAnnotations()[1].sdf_file, kF2);
}

// An ABSOLUTE value in a later file overwrites what an earlier file annotated
// onto the same path of the same instance.
TEST(SdfMultipleFiles, AbsoluteValueOverwritesWhatAnEarlierFileAnnotated) {
  const std::string kF1 =
      WriteSdf("abs_1.sdf", DelayFile(IopathRecord("a", "ABSOLUTE", "5")));
  const std::string kF2 =
      WriteSdf("abs_2.sdf", DelayFile(IopathRecord("a", "ABSOLUTE", "9")));

  Annotated d;
  ASSERT_TRUE(d.Build(CellDesign(kOneInstance, Call(kF1) + Call(kF2))));
  d.Run();

  const PathDelay* path = d.PathOf("a.", "out_z");
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 9u);
}

// An INCREMENT value in a later file modifies what an earlier file annotated
// rather than replacing it.
TEST(SdfMultipleFiles, IncrementValueModifiesWhatAnEarlierFileAnnotated) {
  const std::string kF1 =
      WriteSdf("inc_1.sdf", DelayFile(IopathRecord("a", "ABSOLUTE", "5")));
  const std::string kF2 =
      WriteSdf("inc_2.sdf", DelayFile(IopathRecord("a", "INCREMENT", "3")));

  Annotated d;
  ASSERT_TRUE(d.Build(CellDesign(kOneInstance, Call(kF1) + Call(kF2))));
  d.Run();

  const PathDelay* path = d.PathOf("a.", "out_z");
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 8u);
}

// The same INCREMENT file annotated twice modifies the design twice, which is
// what "each call annotates the design" means when two calls name one file.
TEST(SdfMultipleFiles, RepeatingOneIncrementFileModifiesTheDesignEachTime) {
  const std::string kF1 =
      WriteSdf("rep_1.sdf", DelayFile(IopathRecord("a", "ABSOLUTE", "5")));
  const std::string kF2 =
      WriteSdf("rep_2.sdf", DelayFile(IopathRecord("a", "INCREMENT", "3")));

  Annotated d;
  ASSERT_TRUE(
      d.Build(CellDesign(kOneInstance, Call(kF1) + Call(kF2) + Call(kF2))));
  d.Run();

  const PathDelay* path = d.PathOf("a.", "out_z");
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 11u);
  EXPECT_EQ(d.run_mgr->GetSdfAnnotations().size(), 3u);
}

// Different regions of a design can be annotated from different SDF files, by
// naming the region's hierarchy scope as the second argument. Each file here
// carries a record for both instances, and each call takes only the record that
// falls inside the region it names.
TEST(SdfMultipleFiles,
     SecondArgumentAnnotatesDifferentRegionsFromDifferentFiles) {
  const std::string kF1 =
      WriteSdf("region_1.sdf", DelayFile(IopathRecord("a", "ABSOLUTE", "10") +
                                         IopathRecord("b", "ABSOLUTE", "11")));
  const std::string kF2 =
      WriteSdf("region_2.sdf", DelayFile(IopathRecord("a", "ABSOLUTE", "20") +
                                         IopathRecord("b", "ABSOLUTE", "21")));

  Annotated d;
  ASSERT_TRUE(d.Build(CellDesign(
      kTwoInstances, CallInScope(kF1, "top.a") + CallInScope(kF2, "top.b"))));
  d.Run();

  // Instance a took its delay from the first file only, and instance b from
  // the second file only.
  const PathDelay* from_first = d.PathOf("a.", "out_z");
  ASSERT_NE(from_first, nullptr);
  EXPECT_EQ(from_first->delays[0], 10u);
  const PathDelay* from_second = d.PathOf("b.", "out_z");
  ASSERT_NE(from_second, nullptr);
  EXPECT_EQ(from_second->delays[0], 21u);
}

// Two files, the later one INCREMENT, aimed at two different regions: the
// increment modifies only the region it names, so the other region keeps the
// value the earlier file gave it without any increment applied.
TEST(SdfMultipleFiles, IncrementInALaterFileReachesOnlyTheRegionItNames) {
  const std::string kF1 = WriteSdf(
      "regioninc_1.sdf", DelayFile(IopathRecord("a", "ABSOLUTE", "4") +
                                   IopathRecord("b", "ABSOLUTE", "4")));
  const std::string kF2 = WriteSdf(
      "regioninc_2.sdf", DelayFile(IopathRecord("a", "INCREMENT", "6") +
                                   IopathRecord("b", "INCREMENT", "6")));

  Annotated d;
  ASSERT_TRUE(d.Build(
      CellDesign(kTwoInstances, Call(kF1) + CallInScope(kF2, "top.a"))));
  d.Run();

  const PathDelay* incremented = d.PathOf("a.", "out_z");
  ASSERT_NE(incremented, nullptr);
  EXPECT_EQ(incremented->delays[0], 10u);
  const PathDelay* untouched = d.PathOf("b.", "out_z");
  ASSERT_NE(untouched, nullptr);
  EXPECT_EQ(untouched->delays[0], 4u);
}

// A design whose annotatable value is a timing check constraint rather than a
// module path delay, so what one file left for a later file to overwrite is a
// constraint limit. The check is declared in the cell the SDF names, as the
// module paths above are.
std::string CheckDesign(const std::string& calls) {
  return "module check_leaf(input d_in, input clk_in, output q_out);\n"
         "  specify\n"
         "    $setup(d_in, posedge clk_in, 5);\n"
         "  endspecify\n"
         "endmodule\n"
         "module top;\n"
         "  logic q_wire;\n"
         "  check_leaf a(1'b0, 1'b0, q_wire);\n"
         "  initial begin\n" +
         calls + "  end\nendmodule\n";
}

std::string CheckRecord(const std::string& limit) {
  return "(DELAYFILE (CELL (CELLTYPE \"check_leaf\") (INSTANCE top/a)"
         " (TIMINGCHECK (SETUP d_in (posedge clk_in) (" +
         limit + ")))))";
}

// "Annotated values" is not confined to module path delays: a constraint limit
// an earlier file annotated is overwritten by a later file's ABSOLUTE value the
// same way a delay is.
TEST(SdfMultipleFiles, AbsoluteValueOverwritesAConstraintFromAnEarlierFile) {
  const std::string kF1 = WriteSdf("check_1.sdf", CheckRecord("12"));
  const std::string kF2 = WriteSdf("check_2.sdf", CheckRecord("30"));

  Annotated d;
  ASSERT_TRUE(d.Build(CheckDesign(Call(kF1) + Call(kF2))));
  d.AddTimingChecksOf(d.Cell());
  ASSERT_NE(d.Check(TimingCheckKind::kSetup), nullptr);
  ASSERT_EQ(d.Check(TimingCheckKind::kSetup)->limit, 5u);

  d.Run();

  EXPECT_EQ(d.Check(TimingCheckKind::kSetup)->limit, 30u);
}

// A design whose annotatable value is a specparam, the third category of value
// a run of SDF files can leave state in. The specparam and the module path
// reading it are declared in the top module, and the SDF cell names that module
// by its own name with no instance path below it, so the two meet at the empty
// PathDelay::inst_prefix a module elaborated as a top carries.
std::string SpecparamDesign(const std::string& calls) {
  return "module top(input a_in, output z_out);\n"
         "  specify\n"
         "    specparam cap = 4;\n"
         "    (a_in => z_out) = cap;\n"
         "  endspecify\n"
         "  initial begin\n" +
         calls + "  end\nendmodule\n";
}

std::string LabelRecord(const std::string& section, const std::string& value) {
  return "(DELAYFILE (CELL (CELLTYPE \"top\") (INSTANCE top) (LABEL (" +
         section + " (cap " + value + ")))))";
}

// A later file's INCREMENT modifies the specparam value an earlier file
// annotated, and the module path delay whose expression reads that specparam
// follows it, so the modification is visible on both.
TEST(SdfMultipleFiles, IncrementModifiesASpecparamFromAnEarlierFile) {
  const std::string kF1 =
      WriteSdf("label_1.sdf", LabelRecord("ABSOLUTE", "20"));
  const std::string kF2 =
      WriteSdf("label_2.sdf", LabelRecord("INCREMENT", "7"));

  Annotated d;
  ASSERT_TRUE(d.Build(SpecparamDesign(Call(kF1) + Call(kF2))));
  d.BindSpecparamsOf(d.Top());
  const PathDelay* declared = d.PathOf("", "z_out");
  ASSERT_NE(declared, nullptr);
  ASSERT_EQ(declared->delays[0], 4u);

  d.Run();

  EXPECT_EQ(d.Specparam("cap"), 27u);
  const PathDelay* annotated = d.PathOf("", "z_out");
  ASSERT_NE(annotated, nullptr);
  EXPECT_EQ(annotated->delays[0], 27u);
}

}  // namespace
