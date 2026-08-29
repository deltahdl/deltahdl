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
// first three cases here are the ones that need the prefix: a LABEL reaching
// the specparam of an instantiated cell, the rebuild replacing that instance's
// path rather than adding a second one beside it, and a LABEL naming one of
// two instances leaving the other where it was declared. Each runs a real
// design through $sdf_annotate and reads back the SpecifyManager the run
// installed, SimContext::GetSpecifyManager, since that is the only manager
// whose module paths carry the prefixes RegisterSpecifyBlocks in
// src/simulator/specify_register.cpp filed them under.
//
// The cell those three run, spec_leaf, declares its path delay at 6 and every
// annotated value differs from 6 and from every other value the file writes: 19
// where one instance is annotated, 27 where the count is the reading, and 43
// where one of two instances is annotated and the other must stay at 6. So an
// instance holding its declaration, an instance holding the value meant for its
// sibling, and an instance holding a value carried over from another case's SDF
// file are three different readings. No case reads a delay off a lookup that
// answers 0 when it finds nothing: PathOfInstance answers a pointer, which each
// case asserts on before reading through it.
//
// The other declaration site is issue #3396, and the last three cases are its.
// §6.20.5 permits a specparam "both within the specify block (see Clause 30)
// and in the main module body", and §32.4.3 states no exception for either
// site, while RegisterSpecparams in src/simulator/specify_register.cpp walks
// the SpecifyItemKind::kSpecparam items of the specify blocks it is given and
// so reaches the first site alone. A specparam declared in the module body is
// bound to no SpecifyManager, so SpecifyManager::IsDeclaredSpecparam answers
// false for it and ApplyAnnotatedSpecparam returns before writing anything.
// With the last three cases the file covers both of §6.20.5's sites.
//
// Two further cells carry them. spec_body declares its one specparam in the
// module body alone, at 11, and a LABEL annotates it to 23 where the reading is
// the delay the path takes and to 29 where the reading is the binding instead.
// spec_pair declares one specparam at each site, tbody at 13 in the module body
// and tspec at 17 inside the specify block, each read by its own module path,
// and one LABEL section annotates them to 37 and 41: a fix that walked the
// module body in place of the specify block would leave tspec at 17, and
// reading both paths of the one instance is what says so. None of 11, 13, 17,
// 23, 29, 37 and 41 is 0, and no two quantities any case tells apart share a
// value, so no reading here is satisfied by a lookup that found nothing or by a
// value another declaration or another case's SDF file supplied.

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

// One entry of a LABEL section's ABSOLUTE list: the specparam `name` and the
// value `value` being annotated to it.
std::string LabelEntry(std::string_view name, unsigned value) {
  std::string text = "(";
  text.append(name).append(" ").append(std::to_string(value)).append(")");
  return text;
}

// A whole SDF file whose one CELL record annotates the `cell_type` instance
// `instance_path` from a LABEL section carrying `entries`, which LabelEntry
// writes one of. `instance_path` carries the '/' dividers §32.9 gives an SDF
// instance path and is written from the design root down, so instance i_alpha
// of the top module board is spelled "board/i_alpha".
std::string LabelFileText(std::string_view cell_type,
                          std::string_view instance_path,
                          const std::string& entries) {
  std::string text = "(DELAYFILE (CELL (CELLTYPE \"";
  text.append(cell_type).append("\") (INSTANCE ");
  text.append(instance_path).append(") (LABEL (ABSOLUTE ");
  text.append(entries).append(")))))");
  return text;
}

// A cell declaring a specparam inside its specify block and reading it as the
// delay of its one module path. That is the declaration site
// RegisterSpecifyBlocks walks.
constexpr std::string_view kLeafCell =
    "module spec_leaf(input in_p, output out_p);\n"
    "  specify\n"
    "    specparam tprop = 6;\n"
    "    (in_p => out_p) = tprop;\n"
    "  endspecify\n"
    "endmodule\n";

// A cell declaring its one specparam in the module body, outside every specify
// block, and reading it as the delay of its one module path. §6.20.5 admits
// that site as it admits the one kLeafCell uses, and requires only that the
// declaration precede the reference.
constexpr std::string_view kBodyCell =
    "module spec_body(input in_p, output out_p);\n"
    "  specparam tbody = 11;\n"
    "  specify\n"
    "    (in_p => out_p) = tbody;\n"
    "  endspecify\n"
    "endmodule\n";

// A cell declaring one specparam at each of §6.20.5's two sites, each read by
// its own module path, so one instance holds both. §30.4.1 has a module path
// source be a net connected to an input port and its destination a net
// connected to an output port, which in_p, in_q, out_p and out_q are.
constexpr std::string_view kPairCell =
    "module spec_pair(input in_p, input in_q, output out_p, output out_q);\n"
    "  specparam tbody = 13;\n"
    "  specify\n"
    "    specparam tspec = 17;\n"
    "    (in_p => out_p) = tbody;\n"
    "    (in_q => out_q) = tspec;\n"
    "  endspecify\n"
    "endmodule\n";

// The design a case runs: the cell declarations `cells` writes, the module
// board holding the instantiations `instances` writes, and a $sdf_annotate call
// naming `sdf_path`. board is declared last, so it is the module SdfDesign::
// Lower elaborates as the top, and the SDF instance path of an instance
// declared here begins "board/".
std::string DesignOf(std::string_view cells, const std::string& instances,
                     const std::string& sdf_path) {
  std::string src(cells);
  src.append("module board;\n");
  src.append(instances);
  src.append("  initial $sdf_annotate(\"").append(sdf_path).append("\");\n");
  src.append("endmodule\n");
  return src;
}

// The same design around kLeafCell alone.
std::string BoardOf(const std::string& instances, const std::string& sdf_path) {
  return DesignOf(kLeafCell, instances, sdf_path);
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

  // The module path running from `src_port` that the instance whose
  // hierarchical prefix is `prefix` declared, or null where the run registered
  // none. §30.4 names a path's terminals by the declaring module's own port
  // names, so the prefix is the whole of what separates one instance's path
  // from another's, and the source port is the whole of what separates two
  // paths of one instance.
  const PathDelay* PathOfInstance(std::string_view prefix,
                                  std::string_view src_port = "in_p") const {
    for (const auto& entry : mgr->GetPathDelays()) {
      if (entry.inst_prefix != prefix) continue;
      if (entry.src_port == src_port) return &entry;
    }
    return nullptr;
  }

  // Whether the run bound `name`, declared by the instance whose hierarchical
  // prefix is `prefix`, as a specparam of the design. §32.4.3 has a LABEL
  // annotate to specparams, so a name absent from
  // SpecifyManager::GetDeclaredSpecparamsWithInstance is a name no LABEL can
  // reach, whatever the design otherwise does with it.
  bool BoundSpecparam(std::string_view prefix, std::string_view name) const {
    for (const auto& declared : mgr->GetDeclaredSpecparamsWithInstance()) {
      if (declared.inst_prefix == prefix && declared.name == name) return true;
    }
    return false;
  }
};

// §32.4.3: a LABEL section annotates to the specparams of the cell its CELL
// record names, and the module path delay expression reading one of them is
// reevaluated, so the instance's path holds the delay the annotated value
// produces rather than the delay its declaration produced.
TEST(SdfLabelInsideAnInstance, LabelReachesASpecparamOfAnInstantiatedCell) {
  const std::string kSdf = SdfWrittenFor(
      "reaches",
      LabelFileText("spec_leaf", "board/i_alpha", LabelEntry("tprop", 19)));

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
  const std::string kSdf = SdfWrittenFor(
      "replaces",
      LabelFileText("spec_leaf", "board/i_alpha", LabelEntry("tprop", 27)));

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
  const std::string kSdf = SdfWrittenFor(
      "sibling",
      LabelFileText("spec_leaf", "board/i_alpha", LabelEntry("tprop", 43)));

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

// §32.4.3 with §6.20.5: a specparam declared in the main module body is a
// specparam of the cell as much as one declared inside its specify block, and
// §32.4.3 states no exception for either site. So a LABEL section naming it
// reaches it, and the module path whose delay expression reads it takes the
// delay the annotated value produces rather than the 11 the declaration gave.
TEST(SdfLabelInsideAnInstance, LabelReachesASpecparamDeclaredInTheModuleBody) {
  const std::string kSdf = SdfWrittenFor(
      "body",
      LabelFileText("spec_body", "board/i_body", LabelEntry("tbody", 23)));

  LabelledRun run;
  ASSERT_TRUE(run.Start(
      DesignOf(kBodyCell,
               "  logic body_o;\n  spec_body i_body(1'b0, body_o);\n", kSdf)));

  const PathDelay* annotated = run.PathOfInstance("i_body.");
  ASSERT_NE(annotated, nullptr);
  EXPECT_EQ(annotated->delays[0], 23u);
}

// §32.4.3: a LABEL annotates to the specparams the design declared, so the
// manager has to hold the module-body declaration in the first place --
// SpecifyManager::ApplyAnnotatedSpecparam consults
// SpecifyManager::IsDeclaredSpecparam and returns without writing when the name
// is absent. Reading the binding rather than a delay is what separates a
// specparam that was never bound from one that was bound and not reached.
TEST(SdfLabelInsideAnInstance,
     ModuleBodySpecparamIsBoundToTheManagerUnderItsInstance) {
  const std::string kSdf = SdfWrittenFor(
      "bound",
      LabelFileText("spec_body", "board/i_body", LabelEntry("tbody", 29)));

  LabelledRun run;
  ASSERT_TRUE(run.Start(
      DesignOf(kBodyCell,
               "  logic body_o;\n  spec_body i_body(1'b0, body_o);\n", kSdf)));

  EXPECT_TRUE(run.BoundSpecparam("i_body.", "tbody"));
}

// §6.20.5 permits a specparam within the specify block and in the main module
// body, and §32.4.3 annotates to the specparams the cell declares without
// distinguishing the two sites. One cell declaring tbody in its body and tspec
// inside its specify block, each read by its own module path, therefore takes
// both values of one LABEL section: reading only one site would leave the
// other path at its declaration.
TEST(SdfLabelInsideAnInstance, LabelReachesASpecparamAtEachDeclarationSite) {
  const std::string kSdf = SdfWrittenFor(
      "both",
      LabelFileText("spec_pair", "board/i_pair",
                    LabelEntry("tbody", 37) + " " + LabelEntry("tspec", 41)));

  LabelledRun run;
  ASSERT_TRUE(run.Start(DesignOf(kPairCell,
                                 "  logic pair_p_o;\n  logic pair_q_o;\n"
                                 "  spec_pair i_pair(1'b0, 1'b0, pair_p_o, "
                                 "pair_q_o);\n",
                                 kSdf)));

  const PathDelay* from_body = run.PathOfInstance("i_pair.", "in_p");
  ASSERT_NE(from_body, nullptr);
  ASSERT_EQ(from_body->delays[0], 37u);

  const PathDelay* from_block = run.PathOfInstance("i_pair.", "in_q");
  ASSERT_NE(from_block, nullptr);
  EXPECT_EQ(from_block->delays[0], 41u);
}

}  // namespace
