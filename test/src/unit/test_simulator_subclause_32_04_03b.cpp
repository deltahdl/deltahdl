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

std::string SdfWrittenFor(std::string_view stem, const std::string& text) {
  std::string path = "/tmp/delta_c32_04_03b_";
  path.append(stem).append(".sdf");
  std::ofstream(path, std::ios::trunc) << text;
  return path;
}

std::string LabelEntry(std::string_view name, unsigned value) {
  std::string text = "(";
  text.append(name).append(" ").append(std::to_string(value)).append(")");
  return text;
}

std::string LabelFileText(std::string_view cell_type,
                          std::string_view instance_path,
                          const std::string& entries) {
  std::string text = "(DELAYFILE (CELL (CELLTYPE \"";
  text.append(cell_type).append("\") (INSTANCE ");
  text.append(instance_path).append(") (LABEL (ABSOLUTE ");
  text.append(entries).append(")))))");
  return text;
}

constexpr std::string_view kLeafCell =
    "module spec_leaf(input in_p, output out_p);\n"
    "  specify\n"
    "    specparam tprop = 6;\n"
    "    (in_p => out_p) = tprop;\n"
    "  endspecify\n"
    "endmodule\n";

constexpr std::string_view kBodyCell =
    "module spec_body(input in_p, output out_p);\n"
    "  specparam tbody = 11;\n"
    "  specify\n"
    "    (in_p => out_p) = tbody;\n"
    "  endspecify\n"
    "endmodule\n";

constexpr std::string_view kPairCell =
    "module spec_pair(input in_p, input in_q, output out_p, output out_q);\n"
    "  specparam tbody = 13;\n"
    "  specify\n"
    "    specparam tspec = 17;\n"
    "    (in_p => out_p) = tbody;\n"
    "    (in_q => out_q) = tspec;\n"
    "  endspecify\n"
    "endmodule\n";

std::string DesignOf(std::string_view cells, const std::string& instances,
                     const std::string& sdf_path) {
  std::string src(cells);
  src.append("module board;\n");
  src.append(instances);
  src.append("  initial $sdf_annotate(\"").append(sdf_path).append("\");\n");
  src.append("endmodule\n");
  return src;
}

std::string BoardOf(const std::string& instances, const std::string& sdf_path) {
  return DesignOf(kLeafCell, instances, sdf_path);
}

struct LabelledRun {
  SdfDesign lowered;
  SpecifyManager* mgr = nullptr;

  bool Start(const std::string& src) {
    if (!lowered.Lower(src)) return false;
    mgr = lowered.f.ctx.GetSpecifyManager();
    if (mgr != nullptr) lowered.f.scheduler.Run();
    return mgr != nullptr;
  }

  const PathDelay* PathOfInstance(std::string_view prefix,
                                  std::string_view src_port = "in_p") const {
    for (const auto& entry : mgr->GetPathDelays()) {
      if (entry.inst_prefix != prefix) continue;
      if (entry.src_port == src_port) return &entry;
    }
    return nullptr;
  }

  bool BoundSpecparam(std::string_view prefix, std::string_view name) const {
    for (const auto& declared : mgr->GetDeclaredSpecparamsWithInstance()) {
      if (declared.inst_prefix == prefix && declared.name == name) return true;
    }
    return false;
  }
};

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

TEST(SdfLabelInsideAnInstance, SpecparamReadingTheAnnotatedOneFollowsIt) {
  const std::string kSdf = SdfWrittenFor(
      "chain",
      LabelFileText("spec_chain", "board/i_chain", LabelEntry("a", 5)));

  LabelledRun run;
  ASSERT_TRUE(run.Start(DesignOf(
      "module spec_chain(input in_p, output out_p);\n"
      "  specify\n"
      "    specparam a = 2;\n"
      "    specparam b = a * 3;\n"
      "    (in_p => out_p) = b;\n"
      "  endspecify\n"
      "endmodule\n",
      "  logic chain_o;\n  spec_chain i_chain(1'b0, chain_o);\n", kSdf)));

  const PathDelay* path = run.PathOfInstance("i_chain.");
  ASSERT_NE(path, nullptr);
  EXPECT_EQ(path->delays[0], 15u);
}

}  // namespace
