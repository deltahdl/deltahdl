#include <gtest/gtest.h>

#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_local_variable_flow.h"
#include "elaborator/annex_f_sequence_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

using namespace delta;

namespace {

// A single alphabet letter carrying the given atomic propositions.
Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

// A Boolean leaf sequence b.
auto Bool(const std::string& name) { return SeqBoolean(BoolAtom(name)); }

// A local-variable sampling sequence (1, v = e).
auto Samp(const std::string& name) { return SeqLocalVarSampling(name); }

using NameSet = std::set<std::string>;

// True when two output-context collections describe the same set of contexts.
bool SameContexts(const std::vector<LocalContext>& lhs,
                  const std::vector<LocalContext>& rhs) {
  if (lhs.size() != rhs.size()) {
    return false;
  }
  for (const LocalContext& a : lhs) {
    bool found = false;
    for (const LocalContext& b : rhs) {
      if (LocalContextEqual(a, b)) {
        found = true;
        break;
      }
    }
    if (!found) {
      return false;
    }
  }
  return true;
}

// §F.5.5 (C1): dom(L), L|_D, L\v, and L[v] are the domain and the three domain
// restrictions the rest of the subclause builds on.
TEST(TightSatisfactionLocals, ContextDomainAndRestrictions) {
  const LocalContext ctx{{"v", A({"x"})}, {"w", A({"y"})}};
  EXPECT_EQ(ContextDomain(ctx), (NameSet{"v", "w"}));
  EXPECT_TRUE(LocalContextEqual(RestrictContext(ctx, {"v"}),
                                LocalContext{{"v", A({"x"})}}));
  EXPECT_TRUE(
      LocalContextEqual(RemoveName(ctx, "v"), LocalContext{{"w", A({"y"})}}));
  EXPECT_TRUE(LocalContextEqual(RestrictToName(ctx, "w"),
                                LocalContext{{"w", A({"y"})}}));
  EXPECT_TRUE(LocalContextEqual(RestrictToName(ctx, "absent"), LocalContext{}));
}

// §F.5.5 (C1): LetterEqual compares alphabet elements; T and _|_ are distinct
// from each other and from any atom set.
TEST(TightSatisfactionLocals, LetterEquality) {
  EXPECT_TRUE(LetterEqual(A({"x"}), A({"x"})));
  EXPECT_FALSE(LetterEqual(A({"x"}), A({"y"})));
  EXPECT_TRUE(LetterEqual(LetterTop(), LetterTop()));
  EXPECT_FALSE(LetterEqual(LetterTop(), LetterBottom()));
  EXPECT_FALSE(LetterEqual(LetterTop(), A({"x"})));
}

// §F.5.5 (R3): w, L_0, L_1 |== b iff |w| = 1 and w^0 |= b[L_0] and L_1 = L_0.
// A Boolean leaves the context untouched and matches exactly one letter.
TEST(TightSatisfactionLocals, BooleanPreservesContextAndNeedsOneLetter) {
  const LocalContext input{{"w", A({"y"})}};
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"a"})}, *Bool("a"), input), {input}));
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"x"})}, *Bool("a"), input).empty());
  EXPECT_TRUE(TightSatisfactionOutputs(Word{}, *Bool("a"), input).empty());
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"a"}), A({"a"})}, *Bool("a"), input)
          .empty());
}

// §F.5.5 (R2): w, L_0, L_1 |== (1, v = e) iff |w| = 1 and L_1 binds v to the
// value observed at that letter, keeping the rest of L_0; a prior v is
// overwritten.
TEST(TightSatisfactionLocals, SamplingBindsObservedValue) {
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"})}, *Samp("v"), LocalContext{}),
      {LocalContext{{"v", A({"x"})}}}));
  EXPECT_TRUE(
      SameContexts(TightSatisfactionOutputs(Word{A({"x"})}, *Samp("v"),
                                            LocalContext{{"w", A({"y"})}}),
                   {LocalContext{{"w", A({"y"})}, {"v", A({"x"})}}}));
  EXPECT_TRUE(
      SameContexts(TightSatisfactionOutputs(Word{A({"x"})}, *Samp("v"),
                                            LocalContext{{"v", A({"old"})}}),
                   {LocalContext{{"v", A({"x"})}}}));
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{}, *Samp("v"), LocalContext{}).empty());
}

// §F.5.5 (R1): w, L_0, L_1 |== (t v; R) restores the outer binding of v after
// the body and discards whatever the body assigned to v.
TEST(TightSatisfactionLocals, LocalDeclScopesTheDeclaredName) {
  auto decl = SeqLocalVarDecl("int", "v", Samp("v"));
  // No outer v: the body's v does not escape the declaration.
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"})}, *decl, LocalContext{}),
      {LocalContext{}}));
  // An outer v is restored to its incoming value.
  EXPECT_TRUE(
      SameContexts(TightSatisfactionOutputs(Word{A({"x"})}, *decl,
                                            LocalContext{{"v", A({"old"})}}),
                   {LocalContext{{"v", A({"old"})}}}));
  // A different incoming name survives the declaration unchanged.
  EXPECT_TRUE(
      SameContexts(TightSatisfactionOutputs(Word{A({"x"})}, *decl,
                                            LocalContext{{"w", A({"y"})}}),
                   {LocalContext{{"w", A({"y"})}}}));
}

// §F.5.5 (R4): w, L_0, L_1 |== (R) iff w, L_0, L_1 |== R.
TEST(TightSatisfactionLocals, ParenthesisIsTransparent) {
  EXPECT_TRUE(
      SameContexts(TightSatisfactionOutputs(
                       Word{A({"x"})}, *SeqParen(Samp("v")), LocalContext{}),
                   {LocalContext{{"v", A({"x"})}}}));
}

// §F.5.5 (R5): w, L_0, L_1 |== (R1 ##1 R2) threads the context from R1 into R2
// across the word split.
TEST(TightSatisfactionLocals, ConcatThreadsContextAcrossSplit) {
  auto seq = SeqConcat(Samp("v"), Samp("w"));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"}), A({"y"})}, *seq, LocalContext{}),
      {LocalContext{{"v", A({"x"})}, {"w", A({"y"})}}}));
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"x"})}, *seq, LocalContext{}).empty());
}

// §F.5.5 (R6): w, L_0, L_1 |== (R1 ##0 R2) overlaps the operands on one letter
// and threads the context through that overlap.
TEST(TightSatisfactionLocals, FusionOverlapsOneLetterAndThreadsContext) {
  auto seq = SeqFusion(Samp("v"), Bool("a"));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"a"})}, *seq, LocalContext{}),
      {LocalContext{{"v", A({"a"})}}}));
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"a"}), A({"a"})}, *seq, LocalContext{})
          .empty());
}

// §F.5.5 (R7): w, L_0, L_1 |== (R1 or R2) yields L'|_D with
// D = flow(dom(L_0), (R1 or R2)). A name escaping only one alternative does
// not flow out, but a name produced by both does.
TEST(TightSatisfactionLocals, OrRestrictsToFlowDomain) {
  // v and w each escape only one branch, so neither flows out.
  auto disagree = SeqOr(Samp("v"), Samp("w"));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"})}, *disagree, LocalContext{}),
      {LocalContext{}}));
  // The same name produced by both branches flows out.
  auto agree = SeqOr(Samp("v"), Samp("v"));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"})}, *agree, LocalContext{}),
      {LocalContext{{"v", A({"x"})}}}));
}

// §F.5.5 (R8): w, L_0, L_1 |== (R1 intersect R2) keeps each operand's flow
// minus the blocked and cross-sampled names. Distinct names from both operands
// flow out together.
TEST(TightSatisfactionLocals, IntersectKeepsDistinctNamesFromBothOperands) {
  auto seq = SeqIntersect(Samp("v"), Samp("w"));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"})}, *seq, LocalContext{}),
      {LocalContext{{"v", A({"x"})}, {"w", A({"x"})}}}));
}

// §F.5.5 (R8) with the block/sample subtraction: a name sampled in both
// operands is blocked, so it does not flow out even though each operand binds
// it. The §F.5.5 remark guarantees the surviving union is a function.
TEST(TightSatisfactionLocals, IntersectBlocksCommonlySampledName) {
  auto seq = SeqIntersect(Samp("v"), Samp("v"));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"})}, *seq, LocalContext{}),
      {LocalContext{}}));
}

// §F.5.5 (R9): w, L_0, L_1 |== first_match(R) requires R to match the whole
// word with no shorter prefix matching. The single-letter word matches; the
// two-letter word has a matching prefix, so first_match rejects it.
TEST(TightSatisfactionLocals, FirstMatchRejectsWhenAProperPrefixMatches) {
  auto seq = SeqFirstMatch(SeqUnboundedRepeat(Samp("v")));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"})}, *seq, LocalContext{}),
      {LocalContext{{"v", A({"x"})}}}));
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"x"}), A({"y"})}, *seq, LocalContext{})
          .empty());
}

// §F.5.5 (R10): w, L_0, L_1 |== R[*0] iff |w| = 0 and L_1 = L_0.
TEST(TightSatisfactionLocals, NullRepeatMatchesEmptyWordAndPreservesContext) {
  const LocalContext input{{"w", A({"y"})}};
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{}, *SeqNullRepeat(Samp("v")), input),
      {input}));
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"x"})}, *SeqNullRepeat(Samp("v")), input)
          .empty());
}

// §F.5.5 (R11): w, L_0, L_1 |== R[*1:$] chains the context through each piece,
// so the final binding reflects the last iteration.
TEST(TightSatisfactionLocals, UnboundedRepeatChainsContextThroughPieces) {
  auto seq = SeqUnboundedRepeat(Samp("v"));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"})}, *seq, LocalContext{}),
      {LocalContext{{"v", A({"x"})}}}));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"x"}), A({"y"})}, *seq, LocalContext{}),
      {LocalContext{{"v", A({"y"})}}}));
}

// §F.5.5 (C2): TightlySatisfiesWithLocals is the four-way predicate; it holds
// exactly for the output contexts the relation yields and rejects others.
TEST(TightSatisfactionLocals, FourWayPredicateAcceptsOnlyYieldedContexts) {
  EXPECT_TRUE(TightlySatisfiesWithLocals(Word{A({"x"})}, *Samp("v"),
                                         LocalContext{},
                                         LocalContext{{"v", A({"x"})}}));
  EXPECT_FALSE(TightlySatisfiesWithLocals(Word{A({"x"})}, *Samp("v"),
                                          LocalContext{},
                                          LocalContext{{"v", A({"y"})}}));
  EXPECT_FALSE(TightlySatisfiesWithLocals(Word{A({"x"})}, *Samp("v"),
                                          LocalContext{}, LocalContext{}));
}

// §F.5.5 (C3): every yielded output context has domain flow(dom(L_0), R). Each
// sequence is paired with a word it matches so the check is not vacuous.
TEST(TightSatisfactionLocals, OutputDomainEqualsFlowOfInputDomain) {
  const Letter x = A({"x"});
  const Letter y = A({"y"});
  const std::vector<std::pair<std::shared_ptr<const SequenceExpr>, Word>> cases{
      {Samp("v"), Word{x}},
      {SeqConcat(Samp("v"), Samp("w")), Word{x, y}},
      {SeqOr(Samp("v"), Samp("w")), Word{x}},
      {SeqIntersect(Samp("v"), Samp("w")), Word{x}},
      {SeqLocalVarDecl("int", "v", Samp("v")), Word{x}},
  };
  const LocalContext input{{"u", A({"z"})}};
  for (const auto& item : cases) {
    const NameSet expected = FlowLocals(ContextDomain(input), *item.first);
    const auto outputs =
        TightSatisfactionOutputs(item.second, *item.first, input);
    EXPECT_FALSE(outputs.empty());
    for (const LocalContext& out : outputs) {
      EXPECT_EQ(ContextDomain(out), expected);
    }
  }
}

// §F.5.5 (C4): for a clocked sequence S, w, L_0, L_1 |== S iff the same holds
// for the unclocked rewrite S'. Evaluating S agrees with evaluating S'.
TEST(TightSatisfactionLocals, ClockedSequenceMatchesItsUnclockedRewrite) {
  auto clocked = SeqClock(BoolAtom("clk"), Samp("v"));
  auto unclocked = RewriteClockedSequence(*clocked);
  const std::vector<Letter> alphabet{LetterTop(), A({}), A({"clk"})};
  // Enumerate every word up to length three over the small alphabet.
  std::vector<Word> words{Word{}};
  for (const Letter& l0 : alphabet) {
    words.push_back(Word{l0});
    for (const Letter& l1 : alphabet) {
      words.push_back(Word{l0, l1});
      for (const Letter& l2 : alphabet) {
        words.push_back(Word{l0, l1, l2});
      }
    }
  }
  bool saw_match = false;
  for (const Word& w : words) {
    auto via_clock = TightSatisfactionOutputs(w, *clocked, LocalContext{});
    auto via_rewrite = TightSatisfactionOutputs(w, *unclocked, LocalContext{});
    EXPECT_TRUE(SameContexts(via_clock, via_rewrite));
    saw_match = saw_match || !via_clock.empty();
  }
  EXPECT_TRUE(saw_match);  // the clocked sampling is satisfiable for some word
}

// §F.5.5 (C5): a sequence is nondegenerate iff some nonempty word and contexts
// tightly satisfy it. A sampling and a Boolean are nondegenerate; a sequence
// demanding two incompatible lengths, and R[*0] (only the empty word) are not.
TEST(TightSatisfactionLocals, NondegeneracyReflectsNonemptyMatch) {
  EXPECT_TRUE(IsNondegenerateSequenceWithLocals(*Samp("v")));
  EXPECT_TRUE(IsNondegenerateSequenceWithLocals(*Bool("a")));
  EXPECT_TRUE(
      IsNondegenerateSequenceWithLocals(*SeqClock(BoolAtom("clk"), Samp("v"))));
  auto incompatible = SeqIntersect(Bool("a"), SeqConcat(Bool("a"), Bool("a")));
  EXPECT_FALSE(IsNondegenerateSequenceWithLocals(*incompatible));
  EXPECT_FALSE(IsNondegenerateSequenceWithLocals(*SeqNullRepeat(Bool("a"))));
}

// --- Error conditions and boundary cases ---

// §F.5.5 (R2) edge: when the observed letter is T or _|_, e[L_0, w^0] may be
// any constant of e's type. The sampling still binds v over a one-letter word;
// the observed unknown letter stands in as the bound value.
TEST(TightSatisfactionLocals, SamplingOverUnknownLetterStillBinds) {
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{LetterTop()}, *Samp("v"), LocalContext{}),
      {LocalContext{{"v", LetterTop()}}}));
  EXPECT_TRUE(SameContexts(TightSatisfactionOutputs(Word{LetterBottom()},
                                                    *Samp("v"), LocalContext{}),
                           {LocalContext{{"v", LetterBottom()}}}));
}

// §F.5.5 (R3) edge with §F.5 letter semantics: the top letter T satisfies every
// Boolean (so the context flows through) while the bottom letter _|_ satisfies
// none (so no output context results).
TEST(TightSatisfactionLocals, BooleanMatchesTopRejectsBottom) {
  const LocalContext input{{"w", A({"y"})}};
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{LetterTop()}, *Bool("a"), input), {input}));
  EXPECT_TRUE(TightSatisfactionOutputs(Word{LetterBottom()}, *Bool("a"), input)
                  .empty());
}

// §F.5.5 (R5) boundary: the existential split of (R1 ##1 R2) admits an empty
// left piece, so R1 = R[*0] consumes nothing and R2 matches the whole word.
TEST(TightSatisfactionLocals, ConcatAdmitsEmptyLeftOperand) {
  auto seq = SeqConcat(SeqNullRepeat(Bool("a")), Bool("b"));
  EXPECT_TRUE(SameContexts(
      TightSatisfactionOutputs(Word{A({"b"})}, *seq, LocalContext{}),
      {LocalContext{}}));
}

// §F.5.5 (R6) edge: (R1 ##0 R2) needs a single overlap letter, so the empty
// word can never satisfy a fusion.
TEST(TightSatisfactionLocals, FusionRejectsEmptyWord) {
  auto seq = SeqFusion(Bool("a"), Bool("b"));
  EXPECT_TRUE(TightSatisfactionOutputs(Word{}, *seq, LocalContext{}).empty());
}

// §F.5.5 (R7) error condition: when neither alternative of (R1 or R2) is
// satisfied, the relation yields no output context.
TEST(TightSatisfactionLocals, OrYieldsNothingWhenNoBranchMatches) {
  auto seq = SeqOr(Bool("a"), Bool("b"));
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"c"})}, *seq, LocalContext{}).empty());
}

// §F.5.5 (R8) error condition: (R1 intersect R2) needs both operands satisfied
// by the same word, so operands matching incompatible lengths yield nothing.
TEST(TightSatisfactionLocals, IntersectYieldsNothingForIncompatibleLengths) {
  auto seq = SeqIntersect(Bool("a"), SeqConcat(Bool("a"), Bool("a")));
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"a"})}, *seq, LocalContext{}).empty());
  EXPECT_TRUE(
      TightSatisfactionOutputs(Word{A({"a"}), A({"a"})}, *seq, LocalContext{})
          .empty());
}

// §F.5.5 (R11) edge: R[*1:$] requires at least one piece (j >= 1), so the empty
// word does not satisfy it -- in contrast to R[*0], which only the empty word
// satisfies.
TEST(TightSatisfactionLocals, UnboundedRepeatRejectsEmptyWord) {
  auto seq = SeqUnboundedRepeat(Bool("a"));
  EXPECT_TRUE(TightSatisfactionOutputs(Word{}, *seq, LocalContext{}).empty());
}

}  // namespace
