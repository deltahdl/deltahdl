#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/types.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "lexer/lexer.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/parser.h"
#include "simulator/evaluation.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

struct ParsedSpecify {
  std::vector<const SpecifyPathDecl*> decls;
  RtlirDesign* design = nullptr;
};

ParsedSpecify ElaborateSpecify(const std::string& port_header,
                               const std::string& body, SimFixture& f) {
  std::string code =
      "module t(" + port_header + ");\n" + body + "\nendmodule\n";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  ParsedSpecify out;
  out.design = elab.Elaborate(cu->modules.back()->name);
  for (auto* mod : cu->modules) {
    for (auto* item : mod->items) {
      if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
      for (auto* si : item->specify_items) {
        if (si->kind == SpecifyItemKind::kPathDecl)
          out.decls.push_back(&si->path);
      }
    }
  }
  return out;
}

bool ConditionActive(const SpecifyPathDecl* decl, SimContext& ctx,
                     Arena& arena) {
  if (decl->condition == nullptr) return true;
  Logic4Vec v = EvalExpr(decl->condition, ctx, arena);
  Logic4Word lsb = v.nwords > 0 ? v.words[0] : Logic4Word{};
  return StateDependentPathConditionEnables(lsb);
}

constexpr uint8_t kRiseSlot = 0;
constexpr uint8_t kFallSlot = 1;

TEST(SpecifyDelaySelection, NoCandidatesReturnsZero) {
  std::vector<PathCandidate> candidates;
  EXPECT_EQ(SelectPathDelay(candidates, kRiseSlot), 0u);
}

uint64_t TwoUnconditionalPathsDelay(uint64_t a_time, uint64_t b_time,
                                    size_t slot) {
  SimFixture f;
  auto p = ElaborateSpecify("input a, b, output y",
                            "  specify\n"
                            "    (a => y) = (6, 9);\n"
                            "    (b => y) = (5, 11);\n"
                            "  endspecify",
                            f);
  EXPECT_EQ(p.decls.size(), 2u);
  if (p.decls.size() != 2u) return 0;
  PathDelay a = BuildPathDelayFromDecl(*p.decls[0], f.ctx, f.arena);
  PathDelay b = BuildPathDelayFromDecl(*p.decls[1], f.ctx, f.arena);
  std::vector<PathCandidate> candidates = {{&a, a_time, true},
                                           {&b, b_time, true}};
  return SelectPathDelay(candidates, slot);
}

TEST(SpecifyDelaySelection, UnconditionalPathsAMoreRecentRiseIsSix) {
  EXPECT_EQ(TwoUnconditionalPathsDelay(20, 10, kRiseSlot), 6u);
}

TEST(SpecifyDelaySelection, UnconditionalPathsBMoreRecentRiseIsFive) {
  EXPECT_EQ(TwoUnconditionalPathsDelay(10, 20, kRiseSlot), 5u);
}

TEST(SpecifyDelaySelection, UnconditionalPathsSimultaneousRiseIsSmallest) {
  EXPECT_EQ(TwoUnconditionalPathsDelay(15, 15, kRiseSlot), 5u);
}

TEST(SpecifyDelaySelection, UnconditionalPathsAMoreRecentFallIsNine) {
  EXPECT_EQ(TwoUnconditionalPathsDelay(20, 10, kFallSlot), 9u);
}

std::vector<PathCandidate> BuildModeConditionedCandidates(
    uint64_t mode_value, SimFixture& f, std::vector<PathDelay>& store) {
  std::string body =
      "  logic [7:0] MODE;\n"
      "  wire [5:1] below = {MODE < 5, MODE < 4, MODE < 3, MODE < 2, "
      "MODE < 1};\n"
      "  initial MODE = " +
      std::to_string(mode_value) +
      ";\n"
      "  specify\n"
      "    if (below[5]) (a => y) = (5, 9);\n"
      "    if (below[4]) (a => y) = (4, 8);\n"
      "    if (below[3]) (a => y) = (6, 5);\n"
      "    if (below[2]) (a => y) = (3, 2);\n"
      "    if (below[1]) (a => y) = (7, 7);\n"
      "  endspecify";
  auto p = ElaborateSpecify("input a, output y", body, f);
  LowerAndRun(p.design, f);
  store.clear();
  store.reserve(p.decls.size());
  for (const auto* decl : p.decls) {
    store.push_back(BuildPathDelayFromDecl(*decl, f.ctx, f.arena));
  }
  std::vector<PathCandidate> candidates;
  candidates.reserve(p.decls.size());
  for (size_t i = 0; i < p.decls.size(); ++i) {
    candidates.push_back(
        {&store[i], 10, ConditionActive(p.decls[i], f.ctx, f.arena)});
  }
  return candidates;
}

TEST(SpecifyDelaySelection, ModeConditionedPathsMode2RiseIsFour) {
  SimFixture f;
  std::vector<PathDelay> store;
  auto candidates = BuildModeConditionedCandidates(2, f, store);
  ASSERT_EQ(candidates.size(), 5u);
  EXPECT_EQ(SelectPathDelay(candidates, kRiseSlot), 4u);
}

TEST(SpecifyDelaySelection, ModeConditionedPathsMode2FallIsFive) {
  SimFixture f;
  std::vector<PathDelay> store;
  auto candidates = BuildModeConditionedCandidates(2, f, store);
  ASSERT_EQ(candidates.size(), 5u);
  EXPECT_EQ(SelectPathDelay(candidates, kFallSlot), 5u);
}

TEST(SpecifyDelaySelection, ModeConditionedPathsMode0RiseIsThree) {
  SimFixture f;
  std::vector<PathDelay> store;
  auto candidates = BuildModeConditionedCandidates(0, f, store);
  ASSERT_EQ(candidates.size(), 5u);
  EXPECT_EQ(SelectPathDelay(candidates, kRiseSlot), 3u);
}

TEST(SpecifyDelaySelection, ModeConditionedPathsMode5NoActivePathsReturnsZero) {
  SimFixture f;
  std::vector<PathDelay> store;
  auto candidates = BuildModeConditionedCandidates(5, f, store);
  ASSERT_EQ(candidates.size(), 5u);
  EXPECT_EQ(SelectPathDelay(candidates, kRiseSlot), 0u);
}

TEST(SpecifyDelaySelection, SpecparamDelaysSelectSmallestOnTie) {
  SimFixture f;
  auto p = ElaborateSpecify("input a, b, output y",
                            "  specify\n"
                            "    specparam da = 6, db = 5;\n"
                            "    (a => y) = da;\n"
                            "    (b => y) = db;\n"
                            "  endspecify",
                            f);
  ASSERT_EQ(p.decls.size(), 2u);
  LowerAndRun(p.design, f);
  PathDelay a = BuildPathDelayFromDecl(*p.decls[0], f.ctx, f.arena);
  PathDelay b = BuildPathDelayFromDecl(*p.decls[1], f.ctx, f.arena);
  ASSERT_EQ(a.delays[kRiseSlot], 6u);
  ASSERT_EQ(b.delays[kRiseSlot], 5u);
  std::vector<PathCandidate> candidates = {{&a, 15, true}, {&b, 15, true}};
  EXPECT_EQ(SelectPathDelay(candidates, kRiseSlot), 5u);
}

TEST(SpecifyDelaySelection, XTransitionSlotSelectsSmallestDerivedDelay) {
  constexpr uint8_t kZeroToXSlot = 6;
  SimFixture f;
  auto p = ElaborateSpecify("input a, b, output y",
                            "  specify\n"
                            "    (a => y) = (50, 20, 5, 40, 50, 60);\n"
                            "    (b => y) = (12, 18, 33, 44, 55, 66);\n"
                            "  endspecify",
                            f);
  ASSERT_EQ(p.decls.size(), 2u);
  PathDelay a = BuildPathDelayFromDecl(*p.decls[0], f.ctx, f.arena);
  PathDelay b = BuildPathDelayFromDecl(*p.decls[1], f.ctx, f.arena);
  ASSERT_EQ(a.delays[kZeroToXSlot], 5u);
  ASSERT_EQ(b.delays[kZeroToXSlot], 12u);
  std::vector<PathCandidate> candidates = {{&a, 15, true}, {&b, 15, true}};
  EXPECT_EQ(SelectPathDelay(candidates, kZeroToXSlot), 5u);
  EXPECT_EQ(SelectPathDelay(candidates, kRiseSlot), 12u);
}

}  // namespace
