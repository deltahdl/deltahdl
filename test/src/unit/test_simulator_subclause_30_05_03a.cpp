#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// §30.5.3 selects a delay from among the specify paths that reach one output.
// The value the rule compares is a path delay produced by §30.5.1
// (BuildPathDelayFromDecl) from a real module path assignment, and the
// condition that decides whether a path is active is a real §30.4.4.1
// state-dependent expression. These helpers therefore parse and elaborate a
// genuine specify block and hand back every module path declaration it
// contains, in source order, so the selection rule can be observed on inputs
// built the way the language actually produces them. The only quantity that
// cannot come from source is last_transition_time: it is the simulation time
// at which an input last changed, a scheduler fact, so each test supplies it
// directly.
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

// Evaluates a path's §30.4.4.1 condition the way the runtime would, yielding
// the PathCandidate::condition_true flag. An unconditional path (no `if`) is
// always active; otherwise the parsed expression is evaluated against the
// lowered context and reduced through StateDependentPathConditionEnables.
bool ConditionActive(const SpecifyPathDecl* decl, SimContext& ctx,
                     Arena& arena) {
  if (decl->condition == nullptr) return true;
  Logic4Vec v = EvalExpr(decl->condition, ctx, arena);
  Logic4Word lsb = v.nwords > 0 ? v.words[0] : Logic4Word{};
  return StateDependentPathConditionEnables(lsb);
}

constexpr uint8_t kRiseSlot = 0;  // 0 -> 1 transition column of Table 30-2.
constexpr uint8_t kFallSlot = 1;  // 1 -> 0 transition column of Table 30-2.

// A rule confined to a single stage with no source-produced input: an empty
// candidate set yields no delay.
TEST(SpecifyDelaySelection, NoCandidatesReturnsZero) {
  std::vector<PathCandidate> candidates;
  EXPECT_EQ(SelectPathDelay(candidates, kRiseSlot), 0u);
}

// The delay Example 1's two paths select for `slot`, given the times each of
// the two sources last transitioned.
//
// Both paths -- (a => y) = (6, 9) and (b => y) = (5, 11) -- are built from
// real specify source, so what the rule chooses among is what the assignments
// declared. Returns 0 when the source did not produce the two declarations.
uint64_t Example1Delay(uint64_t a_time, uint64_t b_time, size_t slot) {
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

// --- LRM Example 1: two unconditional paths reach output y. Both path delays
// are built from real (a => y) / (b => y) assignments; the rule picks the delay
// of whichever input transitioned most recently, and the smallest on a tie. ---

TEST(SpecifyDelaySelection, Example1SourceAMoreRecentRiseIsSix) {
  // a transitioned most recently, so only its path is active.
  EXPECT_EQ(Example1Delay(20, 10, kRiseSlot), 6u);
}

TEST(SpecifyDelaySelection, Example1SourceBMoreRecentRiseIsFive) {
  EXPECT_EQ(Example1Delay(10, 20, kRiseSlot), 5u);
}

TEST(SpecifyDelaySelection, Example1SourceSimultaneousRiseIsSmallest) {
  // Simultaneous input transitions leave both paths active; the smaller of the
  // two rise delays (5) is chosen.
  EXPECT_EQ(Example1Delay(15, 15, kRiseSlot), 5u);
}

TEST(SpecifyDelaySelection, Example1SourceAMoreRecentFallIsNine) {
  // The specific transition being scheduled is a fall (1 -> 0); a's fall delay
  // of 9 is used because a transitioned most recently.
  EXPECT_EQ(Example1Delay(20, 10, kFallSlot), 9u);
}

// --- LRM Example 2: five state-dependent paths reach y from the same input a.
// Each `if (MODE < k)` condition is evaluated against the elaborated design, so
// which paths are active is decided by the real §30.4.4.1 machinery. With
// MODE = 2 the first three paths are active; the rule picks the smallest delay
// for the transition being scheduled among exactly those. -------------------

std::vector<PathCandidate> BuildExample2Candidates(
    uint64_t mode_value, SimFixture& f, std::vector<PathDelay>& store) {
  std::string body =
      "  logic [7:0] MODE;\n"
      "  initial MODE = " +
      std::to_string(mode_value) +
      ";\n"
      "  specify\n"
      "    if (MODE < 5) (a => y) = (5, 9);\n"
      "    if (MODE < 4) (a => y) = (4, 8);\n"
      "    if (MODE < 3) (a => y) = (6, 5);\n"
      "    if (MODE < 2) (a => y) = (3, 2);\n"
      "    if (MODE < 1) (a => y) = (7, 7);\n"
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
    // All five paths share input a, so they transition at the same time; their
    // activity is decided purely by the state-dependent condition.
    candidates.push_back(
        {&store[i], 10, ConditionActive(p.decls[i], f.ctx, f.arena)});
  }
  return candidates;
}

TEST(SpecifyDelaySelection, Example2Mode2RiseIsFour) {
  SimFixture f;
  std::vector<PathDelay> store;
  auto candidates = BuildExample2Candidates(2, f, store);
  ASSERT_EQ(candidates.size(), 5u);
  // MODE = 2 activates paths with MODE<5, MODE<4, MODE<3: rise delays 5, 4, 6.
  EXPECT_EQ(SelectPathDelay(candidates, kRiseSlot), 4u);
}

TEST(SpecifyDelaySelection, Example2Mode2FallIsFive) {
  SimFixture f;
  std::vector<PathDelay> store;
  auto candidates = BuildExample2Candidates(2, f, store);
  ASSERT_EQ(candidates.size(), 5u);
  // Same three active paths; fall delays 9, 8, 5 -> smallest is 5.
  EXPECT_EQ(SelectPathDelay(candidates, kFallSlot), 5u);
}

TEST(SpecifyDelaySelection, Example2Mode0RiseIsThree) {
  SimFixture f;
  std::vector<PathDelay> store;
  auto candidates = BuildExample2Candidates(0, f, store);
  ASSERT_EQ(candidates.size(), 5u);
  // MODE = 0 activates all five paths; rise delays 5, 4, 6, 3, 7 -> smallest 3.
  EXPECT_EQ(SelectPathDelay(candidates, kRiseSlot), 3u);
}

TEST(SpecifyDelaySelection, Example2Mode5NoActivePathsReturnsZero) {
  SimFixture f;
  std::vector<PathDelay> store;
  auto candidates = BuildExample2Candidates(5, f, store);
  ASSERT_EQ(candidates.size(), 5u);
  // MODE = 5 satisfies no `MODE < k` condition, so no path is active.
  EXPECT_EQ(SelectPathDelay(candidates, kRiseSlot), 0u);
}

// --- Input form: the delay the rule compares is a constant expression, and a
// specparam takes a different evaluation path than a literal. Both competing
// path delays are named by specparams declared in the specify block and only
// resolve after the design is lowered, so this drives §30.5's specparam
// dependency through the full pipeline before selection runs. ----------------

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
  // Lowering seeds the specparams into the context so BuildPathDelayFromDecl
  // resolves da/db to their declared values.
  LowerAndRun(p.design, f);
  PathDelay a = BuildPathDelayFromDecl(*p.decls[0], f.ctx, f.arena);
  PathDelay b = BuildPathDelayFromDecl(*p.decls[1], f.ctx, f.arena);
  ASSERT_EQ(a.delays[kRiseSlot], 6u);
  ASSERT_EQ(b.delays[kRiseSlot], 5u);
  // Simultaneous transitions keep both paths active; the smaller specparam
  // delay (5) wins.
  std::vector<PathCandidate> candidates = {{&a, 15, true}, {&b, 15, true}};
  EXPECT_EQ(SelectPathDelay(candidates, kRiseSlot), 5u);
}

// --- Input form: the transition being scheduled can be an x transition, so the
// rule indexes an x slot (6..11) rather than rise/fall. Those x-slot delays are
// derived by §30.5.2 from the six explicit delays of each real assignment; the
// selection must compare the correct x-slot delay across the active paths. ----

TEST(SpecifyDelaySelection, XTransitionSlotSelectsSmallestDerivedDelay) {
  constexpr uint8_t kZeroToXSlot = 6;  // 0 -> x column of Table 30-2 / 30-3.
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
  // §30.5.2 derives 0->x as min(0->z, 0->1): a = min(5, 50) = 5, b = min(33,
  // 12) = 12.
  ASSERT_EQ(a.delays[kZeroToXSlot], 5u);
  ASSERT_EQ(b.delays[kZeroToXSlot], 12u);
  std::vector<PathCandidate> candidates = {{&a, 15, true}, {&b, 15, true}};
  // For a 0->x transition the smaller x-slot delay (5) is selected...
  EXPECT_EQ(SelectPathDelay(candidates, kZeroToXSlot), 5u);
  // ...whereas the same active paths select 12 for a rise, confirming the
  // chosen delay tracks the specific transition being scheduled.
  EXPECT_EQ(SelectPathDelay(candidates, kRiseSlot), 12u);
}

}  // namespace
