#include <gtest/gtest.h>

#include "fixture_lexer.h"

using namespace delta;

namespace {

// --- Assertion declaration keywords ---

TEST(AssertionKeywordLexing, PropertyKeyword) {
  auto r = LexOne("property");
  EXPECT_EQ(r.token.kind, TokenKind::kKwProperty);
  EXPECT_EQ(r.token.text, "property");
}

TEST(AssertionKeywordLexing, EndpropertyKeyword) {
  auto r = LexOne("endproperty");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndproperty);
  EXPECT_EQ(r.token.text, "endproperty");
}

TEST(AssertionKeywordLexing, SequenceKeyword) {
  auto r = LexOne("sequence");
  EXPECT_EQ(r.token.kind, TokenKind::kKwSequence);
  EXPECT_EQ(r.token.text, "sequence");
}

TEST(AssertionKeywordLexing, EndsequenceKeyword) {
  auto r = LexOne("endsequence");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEndsequence);
  EXPECT_EQ(r.token.text, "endsequence");
}

TEST(AssertionKeywordLexing, AssertKeyword) {
  auto r = LexOne("assert");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAssert);
  EXPECT_EQ(r.token.text, "assert");
}

TEST(AssertionKeywordLexing, AssumeKeyword) {
  auto r = LexOne("assume");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAssume);
  EXPECT_EQ(r.token.text, "assume");
}

TEST(AssertionKeywordLexing, CoverKeyword) {
  auto r = LexOne("cover");
  EXPECT_EQ(r.token.kind, TokenKind::kKwCover);
  EXPECT_EQ(r.token.text, "cover");
}

TEST(AssertionKeywordLexing, RestrictKeyword) {
  auto r = LexOne("restrict");
  EXPECT_EQ(r.token.kind, TokenKind::kKwRestrict);
  EXPECT_EQ(r.token.text, "restrict");
}

TEST(AssertionKeywordLexing, ExpectKeyword) {
  auto r = LexOne("expect");
  EXPECT_EQ(r.token.kind, TokenKind::kKwExpect);
  EXPECT_EQ(r.token.text, "expect");
}

TEST(AssertionKeywordLexing, StrongKeyword) {
  auto r = LexOne("strong");
  EXPECT_EQ(r.token.kind, TokenKind::kKwStrong);
  EXPECT_EQ(r.token.text, "strong");
}

TEST(AssertionKeywordLexing, WeakKeyword) {
  auto r = LexOne("weak");
  EXPECT_EQ(r.token.kind, TokenKind::kKwWeak);
  EXPECT_EQ(r.token.text, "weak");
}

TEST(AssertionKeywordLexing, DisableKeyword) {
  auto r = LexOne("disable");
  EXPECT_EQ(r.token.kind, TokenKind::kKwDisable);
  EXPECT_EQ(r.token.text, "disable");
}

TEST(AssertionKeywordLexing, IffKeyword) {
  auto r = LexOne("iff");
  EXPECT_EQ(r.token.kind, TokenKind::kKwIff);
  EXPECT_EQ(r.token.text, "iff");
}

TEST(AssertionKeywordLexing, ImpliesKeyword) {
  auto r = LexOne("implies");
  EXPECT_EQ(r.token.kind, TokenKind::kKwImplies);
  EXPECT_EQ(r.token.text, "implies");
}

TEST(AssertionKeywordLexing, FirstMatchKeyword) {
  auto r = LexOne("first_match");
  EXPECT_EQ(r.token.kind, TokenKind::kKwFirstMatch);
  EXPECT_EQ(r.token.text, "first_match");
}

TEST(AssertionKeywordLexing, ThroughoutKeyword) {
  auto r = LexOne("throughout");
  EXPECT_EQ(r.token.kind, TokenKind::kKwThroughout);
  EXPECT_EQ(r.token.text, "throughout");
}

TEST(AssertionKeywordLexing, WithinKeyword) {
  auto r = LexOne("within");
  EXPECT_EQ(r.token.kind, TokenKind::kKwWithin);
  EXPECT_EQ(r.token.text, "within");
}

TEST(AssertionKeywordLexing, IntersectKeyword) {
  auto r = LexOne("intersect");
  EXPECT_EQ(r.token.kind, TokenKind::kKwIntersect);
  EXPECT_EQ(r.token.text, "intersect");
}

TEST(AssertionKeywordLexing, UntypedKeyword) {
  auto r = LexOne("untyped");
  EXPECT_EQ(r.token.kind, TokenKind::kKwUntyped);
  EXPECT_EQ(r.token.text, "untyped");
}

TEST(AssertionKeywordLexing, LocalKeyword) {
  auto r = LexOne("local");
  EXPECT_EQ(r.token.kind, TokenKind::kKwLocal);
  EXPECT_EQ(r.token.text, "local");
}

// --- Property expression keywords ---

TEST(AssertionKeywordLexing, NexttimeKeyword) {
  auto r = LexOne("nexttime");
  EXPECT_EQ(r.token.kind, TokenKind::kKwNexttime);
  EXPECT_EQ(r.token.text, "nexttime");
}

TEST(AssertionKeywordLexing, SNexttimeKeyword) {
  auto r = LexOne("s_nexttime");
  EXPECT_EQ(r.token.kind, TokenKind::kKwSNexttime);
  EXPECT_EQ(r.token.text, "s_nexttime");
}

TEST(AssertionKeywordLexing, SAlwaysKeyword) {
  auto r = LexOne("s_always");
  EXPECT_EQ(r.token.kind, TokenKind::kKwSAlways);
  EXPECT_EQ(r.token.text, "s_always");
}

TEST(AssertionKeywordLexing, UntilKeyword) {
  auto r = LexOne("until");
  EXPECT_EQ(r.token.kind, TokenKind::kKwUntil);
  EXPECT_EQ(r.token.text, "until");
}

TEST(AssertionKeywordLexing, SUntilKeyword) {
  auto r = LexOne("s_until");
  EXPECT_EQ(r.token.kind, TokenKind::kKwSUntil);
  EXPECT_EQ(r.token.text, "s_until");
}

TEST(AssertionKeywordLexing, UntilWithKeyword) {
  auto r = LexOne("until_with");
  EXPECT_EQ(r.token.kind, TokenKind::kKwUntilWith);
  EXPECT_EQ(r.token.text, "until_with");
}

TEST(AssertionKeywordLexing, SUntilWithKeyword) {
  auto r = LexOne("s_until_with");
  EXPECT_EQ(r.token.kind, TokenKind::kKwSUntilWith);
  EXPECT_EQ(r.token.text, "s_until_with");
}

TEST(AssertionKeywordLexing, EventuallyKeyword) {
  auto r = LexOne("eventually");
  EXPECT_EQ(r.token.kind, TokenKind::kKwEventually);
  EXPECT_EQ(r.token.text, "eventually");
}

TEST(AssertionKeywordLexing, SEventuallyKeyword) {
  auto r = LexOne("s_eventually");
  EXPECT_EQ(r.token.kind, TokenKind::kKwSEventually);
  EXPECT_EQ(r.token.text, "s_eventually");
}

TEST(AssertionKeywordLexing, AcceptOnKeyword) {
  auto r = LexOne("accept_on");
  EXPECT_EQ(r.token.kind, TokenKind::kKwAcceptOn);
  EXPECT_EQ(r.token.text, "accept_on");
}

TEST(AssertionKeywordLexing, RejectOnKeyword) {
  auto r = LexOne("reject_on");
  EXPECT_EQ(r.token.kind, TokenKind::kKwRejectOn);
  EXPECT_EQ(r.token.text, "reject_on");
}

TEST(AssertionKeywordLexing, SyncAcceptOnKeyword) {
  auto r = LexOne("sync_accept_on");
  EXPECT_EQ(r.token.kind, TokenKind::kKwSyncAcceptOn);
  EXPECT_EQ(r.token.text, "sync_accept_on");
}

TEST(AssertionKeywordLexing, SyncRejectOnKeyword) {
  auto r = LexOne("sync_reject_on");
  EXPECT_EQ(r.token.kind, TokenKind::kKwSyncRejectOn);
  EXPECT_EQ(r.token.text, "sync_reject_on");
}

// --- Assertion operators ---

TEST(AssertionOperatorLexing, OverlapImplicationOp) {
  auto tokens = Lex("a |-> b");
  bool found = false;
  for (const auto& tok : tokens) {
    if (tok.kind == TokenKind::kPipeDashGt) {
      found = true;
      EXPECT_EQ(tok.text, "|->");
    }
  }
  EXPECT_TRUE(found);
}

TEST(AssertionOperatorLexing, NonoverlapImplicationOp) {
  auto tokens = Lex("a |=> b");
  bool found = false;
  for (const auto& tok : tokens) {
    if (tok.kind == TokenKind::kPipeEqGt) {
      found = true;
      EXPECT_EQ(tok.text, "|=>");
    }
  }
  EXPECT_TRUE(found);
}

TEST(AssertionOperatorLexing, CycleDelayOp) {
  auto tokens = Lex("##1");
  ASSERT_GE(tokens.size(), 1u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kHashHash);
  EXPECT_EQ(tokens[0].text, "##");
}

TEST(AssertionOperatorLexing, FollowedByOverlappedOp) {
  auto tokens = Lex("a #-# b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kHashMinusHash);
  EXPECT_EQ(tokens[1].text, "#-#");
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(AssertionOperatorLexing, FollowedByNonoverlappedOp) {
  auto tokens = Lex("a #=# b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kHashEqHash);
  EXPECT_EQ(tokens[1].text, "#=#");
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(AssertionOperatorLexing, FollowedByOverlappedNoSpaces) {
  auto tokens = Lex("a#-#b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kHashMinusHash);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(AssertionOperatorLexing, FollowedByNonoverlappedNoSpaces) {
  auto tokens = Lex("a#=#b");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kHashEqHash);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(AssertionOperatorLexing, OverlapImplicationInContext) {
  auto tokens = Lex("req |-> ack");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPipeDashGt);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(AssertionOperatorLexing, NonoverlapImplicationInContext) {
  auto tokens = Lex("req |=> ack");
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kIdentifier);
  EXPECT_EQ(tokens[1].kind, TokenKind::kPipeEqGt);
  EXPECT_EQ(tokens[2].kind, TokenKind::kIdentifier);
}

TEST(AssertionOperatorLexing, CycleDelayInSequence) {
  auto tokens = Lex("a ##1 b ##[1:3] c");
  bool found_hash_hash = false;
  int count = 0;
  for (const auto& tok : tokens) {
    if (tok.kind == TokenKind::kHashHash) {
      found_hash_hash = true;
      ++count;
    }
  }
  EXPECT_TRUE(found_hash_hash);
  EXPECT_EQ(count, 2);
}

// --- Keyword used as identifier guard ---

TEST(AssertionKeywordLexing, PropertyNotIdentifier) {
  auto tokens = Lex("property foo");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwProperty);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

TEST(AssertionKeywordLexing, SequenceNotIdentifier) {
  auto tokens = Lex("sequence bar");
  ASSERT_GE(tokens.size(), 2u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kKwSequence);
  EXPECT_EQ(tokens[1].kind, TokenKind::kIdentifier);
}

}  // namespace
