// An SDF LABEL section reaching a specparam that a cell of the design
// declares, rather than one the top module declares.
//
// §32.4.3 has a LABEL section carry new values for the specparams a cell
// declares, and has every expression reading such a specparam reevaluated when
// a value is annotated to it. §30.4 has the specify block that writes such an
// expression name its terminals by the bare port names of the module it stands
// in, so every instance of a cell carries a module path spelled identically to
// every other instance's, and PathDelay::inst_prefix in
// src/simulator/specify_path_delay.h is what tells two of them apart --
// "i_alpha." for instance i_alpha of the top. A specparam is named the same
// way: Lowerer::CreateChildModuleVariables gives instance i_alpha's tprop the
// name "i_alpha.tprop", because every instance of the cell declares one.
//
// Issue #3392 is that neither name was carried. SpecifyManager's
// declared_specparams_ and path_decls_ held bare names with no instance, and
// SpecifyManager::BindDesignSpecparams had no caller under src/ at all, so
// specparam_ctx_ was null in every run and
// SpecifyManager::ApplyAnnotatedSpecparam returned at its first line. A
// specparam living at "i_alpha.tprop" was looked up under "tprop" and found
// nowhere, and a path delay rebuilt from a declaration carrying no prefix was
// appended beside the real path rather than replacing it, because
// SpecifyManager::AddPathDelay compares PathDelay::inst_prefix.
//
// Every case in test_simulator_subclause_32_04_03a.cpp declares its specparam
// in the module elaborated as the top, where there is one instance and the
// prefix is empty either way, and binds the manager by calling
// BindDesignSpecparams itself. None of them can fail on any of the above. The
// three cases here are the ones that need the prefix: a LABEL reaching the
// specparam of an instantiated cell, the rebuild replacing that instance's
// path rather than adding a second one beside it, and a LABEL naming one of
// two instances leaving the other where it was declared. Each runs a real
// design through $sdf_annotate and reads back the SpecifyManager the run
// installed, SimContext::GetSpecifyManager, since that is the only manager
// whose module paths carry the prefixes RegisterSpecifyBlocks in
// src/simulator/specify_register.cpp filed them under.
//
// The cell declares its path delay at 6 and every annotated value differs from
// 6 and from every other value the file writes: 19 where one instance is
// annotated, 27 where the count is the reading, and 43 where one of two
// instances is annotated and the other must stay at 6. So an instance holding
// its declaration, an instance holding the value meant for its sibling, and an
// instance holding a value carried over from another case's SDF file are three
// different readings. No case reads a delay off a lookup that answers 0 when
// it finds nothing: PathOfInstance answers a pointer, which each case asserts
// on before reading through it.

#include <gtest/gtest.h>

#include <fstream>
#include <ios>
#include <string>
#include <string_view>

#include "fixture_sdf_design.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

// Puts `text` on disk under a name derived from `stem` that a $sdf_annotate
// operand can open, and answers that name.
std::string SdfWrittenFor(std::string_view stem, const std::string& text) {
  std::string path = "/tmp/delta_c32_04_03b_";
  path.append(stem).append(".sdf");
  std::ofstream(path, std::ios::trunc) << text;
  return path;
}

// A whole SDF file whose one CELL record annotates the spec_leaf instance
// `instance_path` from a LABEL section giving tprop the value `value`.
// `instance_path` carries the '/' dividers §32.9 gives an SDF instance path
// and is written from the design root down, so instance i_alpha of the top
// module board is spelled "board/i_alpha".
std::string LabelFileText(std::string_view instance_path, unsigned value) {
  std::string text = "(DELAYFILE (CELL (CELLTYPE \"spec_leaf\") (INSTANCE ";
  text.append(instance_path).append(") (LABEL (ABSOLUTE (tprop ");
  text.append(std::to_string(value)).append(")))))");
  return text;
}

// The design a case runs: a cell declaring a specparam and reading it as the
// delay of its one module path, the instantiations `instances` writes, and a
// $sdf_annotate call naming `sdf_path`. The specparam is declared inside the
// specify block, which is the declaration site RegisterSpecifyBlocks walks.
// The top is named board, so the SDF instance path of an instance declared
// here begins "board/".
std::string BoardOf(const std::string& instances, const std::string& sdf_path) {
  std::string src =
      "module spec_leaf(input in_p, output out_p);\n"
      "  specify\n"
      "    specparam tprop = 6;\n"
      "    (in_p => out_p) = tprop;\n"
      "  endspecify\n"
      "endmodule\n"
      "module board;\n";
  src.append(instances);
  src.append("  initial $sdf_annotate(\"").append(sdf_path).append("\");\n");
  src.append("endmodule\n");
  return src;
}

// A design lowered and run, holding the SpecifyManager the run installed:
// SimContext::GetSpecifyManager, which Lowerer::Lower filled through
// SimContext::AcquireSpecifyManager.
struct LabelledRun {
  SdfDesign lowered;
  SpecifyManager* mgr = nullptr;

  bool Start(const std::string& src) {
    if (!lowered.Lower(src)) return false;
    mgr = lowered.f.ctx.GetSpecifyManager();
    if (mgr != nullptr) lowered.f.scheduler.Run();
    return mgr != nullptr;
  }

  // The module path the instance whose hierarchical prefix is `prefix`
  // declared, or null where the run registered none under that prefix. Every
  // path here runs from in_p to out_p, so the prefix is the whole of what
  // separates one instance's path from another's.
  const PathDelay* PathOfInstance(std::string_view prefix) const {
    for (const auto& entry : mgr->GetPathDelays()) {
      if (entry.inst_prefix != prefix) continue;
      if (entry.src_port == "in_p") return &entry;
    }
    return nullptr;
  }
};

// §32.4.3: a LABEL section annotates to the specparams of the cell its CELL
// record names, and the module path delay expression reading one of them is
// reevaluated, so the instance's path holds the delay the annotated value
// produces rather than the delay its declaration produced.
TEST(SdfLabelInsideAnInstance, LabelReachesASpecparamOfAnInstantiatedCell) {
  const std::string kSdf =
      SdfWrittenFor("reaches", LabelFileText("board/i_alpha", 19));

  LabelledRun run;
  ASSERT_TRUE(run.Start(BoardOf(
      "  logic alpha_o;\n  spec_leaf i_alpha(1'b0, alpha_o);\n", kSdf)));

  const PathDelay* annotated = run.PathOfInstance("i_alpha.");
  ASSERT_NE(annotated, nullptr);
  EXPECT_EQ(annotated->delays[0], 19u);
}

// §32.4.3: reevaluating an expression that reads an annotated specparam
// replaces the module path the expression belongs to. The design declares one
// module path, so it still holds one after the annotation; a rebuild that
// filed its result under a prefix the declaration never carried would leave
// the original standing and add a second path beside it, which the delay a
// lookup answers with would not show.
TEST(SdfLabelInsideAnInstance,
     ReevaluationReplacesTheInstancePathRatherThanAddingOne) {
  const std::string kSdf =
      SdfWrittenFor("replaces", LabelFileText("board/i_alpha", 27));

  LabelledRun run;
  ASSERT_TRUE(run.Start(BoardOf(
      "  logic alpha_o;\n  spec_leaf i_alpha(1'b0, alpha_o);\n", kSdf)));

  EXPECT_EQ(run.mgr->PathDelayCount(), 1u);
}

// §32.4.3 with §32.9's CELL record: the LABEL section belongs to the instance
// its CELL record names, so a file naming one of two instances of one cell
// annotates that instance's specparam and leaves the other instance's holding
// what the cell declared. Both instances declare a specparam spelled tprop and
// a module path spelled in_p to out_p, so the instance is the whole of what
// keeps the annotation off the sibling.
TEST(SdfLabelInsideAnInstance,
     LabelNamingOneInstanceLeavesTheOtherInstanceDeclared) {
  const std::string kSdf =
      SdfWrittenFor("sibling", LabelFileText("board/i_alpha", 43));

  LabelledRun run;
  ASSERT_TRUE(
      run.Start(BoardOf("  logic alpha_o;\n  logic beta_o;\n"
                        "  spec_leaf i_alpha(1'b0, alpha_o);\n"
                        "  spec_leaf i_beta(1'b0, beta_o);\n",
                        kSdf)));
  const PathDelay* named = run.PathOfInstance("i_alpha.");
  ASSERT_NE(named, nullptr);
  ASSERT_EQ(named->delays[0], 43u);

  const PathDelay* unnamed = run.PathOfInstance("i_beta.");
  ASSERT_NE(unnamed, nullptr);
  EXPECT_EQ(unnamed->delays[0], 6u);
}

}  // namespace
